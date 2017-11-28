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
      (fun uu___302_107  ->
         match uu___302_107 with
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
        let uu___325_205 = a in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___325_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___325_205.FStar_Syntax_Syntax.sort)
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
          (fun uu____853  ->
             match uu____853 with
             | (names1,uu____865) -> FStar_Util.smap_try_find names1 y1) in
      match uu____748 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____874 ->
          (FStar_Util.incr ctr;
           (let uu____897 =
              let uu____898 =
                let uu____899 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____899 in
              Prims.strcat "__" uu____898 in
            Prims.strcat y1 uu____897)) in
    let top_scope =
      let uu____963 =
        let uu____972 = FStar_ST.op_Bang scopes in FStar_List.hd uu____972 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____963 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1100 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1187 =
      let uu____1188 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1188 in
    FStar_Util.format2 "%s_%s" pfx uu____1187 in
  let string_const s =
    let uu____1193 =
      let uu____1196 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1196
        (fun uu____1298  ->
           match uu____1298 with
           | (uu____1309,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1193 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 () in
        let f =
          let uu____1322 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1322 in
        let top_scope =
          let uu____1326 =
            let uu____1335 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1335 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1326 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1452 =
    let uu____1453 =
      let uu____1464 = new_scope () in
      let uu____1473 = FStar_ST.op_Bang scopes in uu____1464 :: uu____1473 in
    FStar_ST.op_Colon_Equals scopes uu____1453 in
  let pop1 uu____1655 =
    let uu____1656 =
      let uu____1667 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1667 in
    FStar_ST.op_Colon_Equals scopes uu____1656 in
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
    let uu___326_1849 = x in
    let uu____1850 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1850;
      FStar_Syntax_Syntax.index = (uu___326_1849.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___326_1849.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1883 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1919 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____1966 'Auu____1967 .
    'Auu____1967 ->
      ('Auu____1967,'Auu____1966 FStar_Pervasives_Native.option)
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
  'Auu____2263 .
    'Auu____2263 ->
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
                 (fun uu___303_2297  ->
                    match uu___303_2297 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2301 -> [])) in
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
    let uu____2310 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___304_2320  ->
              match uu___304_2320 with
              | Binding_var (x,uu____2322) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2324,uu____2325,uu____2326) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2310 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2340 .
    env_t ->
      (binding -> 'Auu____2340 FStar_Pervasives_Native.option) ->
        'Auu____2340 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2368 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2368
      then
        let uu____2371 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2371
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
      let uu____2384 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2384)
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
        (let uu___327_2400 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___327_2400.tcenv);
           warn = (uu___327_2400.warn);
           cache = (uu___327_2400.cache);
           nolabels = (uu___327_2400.nolabels);
           use_zfuel_name = (uu___327_2400.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___327_2400.encode_non_total_function_typ);
           current_module_name = (uu___327_2400.current_module_name)
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
        (let uu___328_2418 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___328_2418.depth);
           tcenv = (uu___328_2418.tcenv);
           warn = (uu___328_2418.warn);
           cache = (uu___328_2418.cache);
           nolabels = (uu___328_2418.nolabels);
           use_zfuel_name = (uu___328_2418.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___328_2418.encode_non_total_function_typ);
           current_module_name = (uu___328_2418.current_module_name)
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
          (let uu___329_2439 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___329_2439.depth);
             tcenv = (uu___329_2439.tcenv);
             warn = (uu___329_2439.warn);
             cache = (uu___329_2439.cache);
             nolabels = (uu___329_2439.nolabels);
             use_zfuel_name = (uu___329_2439.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___329_2439.encode_non_total_function_typ);
             current_module_name = (uu___329_2439.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___330_2449 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___330_2449.depth);
          tcenv = (uu___330_2449.tcenv);
          warn = (uu___330_2449.warn);
          cache = (uu___330_2449.cache);
          nolabels = (uu___330_2449.nolabels);
          use_zfuel_name = (uu___330_2449.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___330_2449.encode_non_total_function_typ);
          current_module_name = (uu___330_2449.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___305_2473  ->
             match uu___305_2473 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2486 -> FStar_Pervasives_Native.None) in
      let uu____2491 = aux a in
      match uu____2491 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2503 = aux a2 in
          (match uu____2503 with
           | FStar_Pervasives_Native.None  ->
               let uu____2514 =
                 let uu____2515 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2516 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2515 uu____2516 in
               failwith uu____2514
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
      let uu____2543 =
        let uu___331_2544 = env in
        let uu____2545 =
          let uu____2548 =
            let uu____2549 =
              let uu____2562 =
                let uu____2565 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2565 in
              (x, fname, uu____2562, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2549 in
          uu____2548 :: (env.bindings) in
        {
          bindings = uu____2545;
          depth = (uu___331_2544.depth);
          tcenv = (uu___331_2544.tcenv);
          warn = (uu___331_2544.warn);
          cache = (uu___331_2544.cache);
          nolabels = (uu___331_2544.nolabels);
          use_zfuel_name = (uu___331_2544.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___331_2544.encode_non_total_function_typ);
          current_module_name = (uu___331_2544.current_module_name)
        } in
      (fname, ftok, uu____2543)
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
        (fun uu___306_2607  ->
           match uu___306_2607 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2646 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2663 =
        lookup_binding env
          (fun uu___307_2671  ->
             match uu___307_2671 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2686 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2663 FStar_Option.isSome
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
      let uu____2705 = try_lookup_lid env a in
      match uu____2705 with
      | FStar_Pervasives_Native.None  ->
          let uu____2738 =
            let uu____2739 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2739 in
          failwith uu____2738
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
          let uu___332_2787 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___332_2787.depth);
            tcenv = (uu___332_2787.tcenv);
            warn = (uu___332_2787.warn);
            cache = (uu___332_2787.cache);
            nolabels = (uu___332_2787.nolabels);
            use_zfuel_name = (uu___332_2787.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___332_2787.encode_non_total_function_typ);
            current_module_name = (uu___332_2787.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2801 = lookup_lid env x in
        match uu____2801 with
        | (t1,t2,uu____2814) ->
            let t3 =
              let uu____2824 =
                let uu____2831 =
                  let uu____2834 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2834] in
                (f, uu____2831) in
              FStar_SMTEncoding_Util.mkApp uu____2824 in
            let uu___333_2839 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___333_2839.depth);
              tcenv = (uu___333_2839.tcenv);
              warn = (uu___333_2839.warn);
              cache = (uu___333_2839.cache);
              nolabels = (uu___333_2839.nolabels);
              use_zfuel_name = (uu___333_2839.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___333_2839.encode_non_total_function_typ);
              current_module_name = (uu___333_2839.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2852 = try_lookup_lid env l in
      match uu____2852 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2901 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2909,fuel::[]) ->
                         let uu____2913 =
                           let uu____2914 =
                             let uu____2915 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2915
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2914 "fuel" in
                         if uu____2913
                         then
                           let uu____2918 =
                             let uu____2919 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2919
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2918
                         else FStar_Pervasives_Native.Some t
                     | uu____2923 -> FStar_Pervasives_Native.Some t)
                | uu____2924 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2937 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2937 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2941 =
            let uu____2942 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2942 in
          failwith uu____2941
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2953 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2953 with | (x,uu____2965,uu____2966) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2991 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2991 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3027;
                 FStar_SMTEncoding_Term.rng = uu____3028;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3043 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3067 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___308_3083  ->
           match uu___308_3083 with
           | Binding_fvar (uu____3086,nm',tok,uu____3089) when nm = nm' ->
               tok
           | uu____3098 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3102 .
    'Auu____3102 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3120  ->
      match uu____3120 with
      | (pats,vars,body) ->
          let fallback uu____3145 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3150 = FStar_Options.unthrottle_inductives () in
          if uu____3150
          then fallback ()
          else
            (let uu____3152 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3152 with
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
                           | uu____3183 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3204 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3204
                         | uu____3207 ->
                             let uu____3208 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3208 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3213 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3254 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3267 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3274 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3275 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3292 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3309 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3311 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3311 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3329;
             FStar_Syntax_Syntax.vars = uu____3330;_},uu____3331)
          ->
          let uu____3352 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3352 FStar_Option.isNone
      | uu____3369 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3376 =
        let uu____3377 = FStar_Syntax_Util.un_uinst t in
        uu____3377.FStar_Syntax_Syntax.n in
      match uu____3376 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3380,uu____3381,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___309_3402  ->
                  match uu___309_3402 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3403 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3405 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3405 FStar_Option.isSome
      | uu____3422 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3429 = head_normal env t in
      if uu____3429
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
    let uu____3440 =
      let uu____3441 = FStar_Syntax_Syntax.null_binder t in [uu____3441] in
    let uu____3442 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3440 uu____3442 FStar_Pervasives_Native.None
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
                    let uu____3480 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3480
                | s ->
                    let uu____3485 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3485) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___310_3500  ->
    match uu___310_3500 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3501 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3537;
                       FStar_SMTEncoding_Term.rng = uu____3538;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3561) ->
              let uu____3570 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3581 -> false) args (FStar_List.rev xs)) in
              if uu____3570
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3585,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3589 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3593 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3593)) in
              if uu____3589
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3597 -> FStar_Pervasives_Native.None in
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
    | uu____3819 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3823 -> false
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3842 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3855 ->
            let uu____3862 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3862
        | uu____3863 ->
            if norm1
            then let uu____3864 = whnf env t1 in aux false uu____3864
            else
              (let uu____3866 =
                 let uu____3867 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3868 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3867 uu____3868 in
               failwith uu____3866) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3900) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3905 ->
        let uu____3906 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3906)
let is_arithmetic_primitive:
  'Auu____3920 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3920 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3940::uu____3941::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3945::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3948 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3969 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3984 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____3988 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3988)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4027)::uu____4028::uu____4029::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4080)::uu____4081::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4118 -> false
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
          let uu____4325 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4325, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4328 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4328, [])
      | FStar_Const.Const_char c1 ->
          let uu____4332 =
            let uu____4333 =
              let uu____4340 =
                let uu____4343 =
                  let uu____4344 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4344 in
                [uu____4343] in
              ("FStar.Char.__char_of_int", uu____4340) in
            FStar_SMTEncoding_Util.mkApp uu____4333 in
          (uu____4332, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4360 =
            let uu____4361 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4361 in
          (uu____4360, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4382) ->
          let uu____4383 = varops.string_const s in (uu____4383, [])
      | FStar_Const.Const_range uu____4386 ->
          let uu____4387 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4387, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4393 =
            let uu____4394 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4394 in
          failwith uu____4393
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
        (let uu____4423 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4423
         then
           let uu____4424 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4424
         else ());
        (let uu____4426 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4510  ->
                   fun b  ->
                     match uu____4510 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4589 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4605 = gen_term_var env1 x in
                           match uu____4605 with
                           | (xxsym,xx,env') ->
                               let uu____4629 =
                                 let uu____4634 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4634 env1 xx in
                               (match uu____4629 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4589 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4426 with
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
          let uu____4793 = encode_term t env in
          match uu____4793 with
          | (t1,decls) ->
              let uu____4804 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4804, decls)
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
          let uu____4815 = encode_term t env in
          match uu____4815 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4830 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4830, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4832 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4832, decls))
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
        let uu____4838 = encode_args args_e env in
        match uu____4838 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4857 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4866 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4866 in
            let binary arg_tms1 =
              let uu____4879 =
                let uu____4880 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4880 in
              let uu____4881 =
                let uu____4882 =
                  let uu____4883 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4883 in
                FStar_SMTEncoding_Term.unboxInt uu____4882 in
              (uu____4879, uu____4881) in
            let mk_default uu____4889 =
              let uu____4890 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4890 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4941 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4941
              then
                let uu____4942 = let uu____4943 = mk_args ts in op uu____4943 in
                FStar_All.pipe_right uu____4942 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4972 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4972
              then
                let uu____4973 = binary ts in
                match uu____4973 with
                | (t1,t2) ->
                    let uu____4980 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4980
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4984 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4984
                 then
                   let uu____4985 = op (binary ts) in
                   FStar_All.pipe_right uu____4985
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
            let uu____5116 =
              let uu____5125 =
                FStar_List.tryFind
                  (fun uu____5147  ->
                     match uu____5147 with
                     | (l,uu____5157) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5125 FStar_Util.must in
            (match uu____5116 with
             | (uu____5196,op) ->
                 let uu____5206 = op arg_tms in (uu____5206, decls))
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
        let uu____5214 = FStar_List.hd args_e in
        match uu____5214 with
        | (tm_sz,uu____5222) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5232 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5232 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5240 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5240);
                   t_decls) in
            let uu____5241 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5261::(sz_arg,uu____5263)::uu____5264::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5313 =
                    let uu____5316 = FStar_List.tail args_e in
                    FStar_List.tail uu____5316 in
                  let uu____5319 =
                    let uu____5322 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5322 in
                  (uu____5313, uu____5319)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5328::(sz_arg,uu____5330)::uu____5331::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5380 =
                    let uu____5381 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5381 in
                  failwith uu____5380
              | uu____5390 ->
                  let uu____5397 = FStar_List.tail args_e in
                  (uu____5397, FStar_Pervasives_Native.None) in
            (match uu____5241 with
             | (arg_tms,ext_sz) ->
                 let uu____5420 = encode_args arg_tms env in
                 (match uu____5420 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5441 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5450 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5450 in
                      let unary_arith arg_tms2 =
                        let uu____5459 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5459 in
                      let binary arg_tms2 =
                        let uu____5472 =
                          let uu____5473 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5473 in
                        let uu____5474 =
                          let uu____5475 =
                            let uu____5476 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5476 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5475 in
                        (uu____5472, uu____5474) in
                      let binary_arith arg_tms2 =
                        let uu____5491 =
                          let uu____5492 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5492 in
                        let uu____5493 =
                          let uu____5494 =
                            let uu____5495 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5495 in
                          FStar_SMTEncoding_Term.unboxInt uu____5494 in
                        (uu____5491, uu____5493) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5544 =
                          let uu____5545 = mk_args ts in op uu____5545 in
                        FStar_All.pipe_right uu____5544 resBox in
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
                        let uu____5653 =
                          let uu____5656 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5656 in
                        let uu____5658 =
                          let uu____5661 =
                            let uu____5662 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5662 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5661 in
                        mk_bv uu____5653 unary uu____5658 arg_tms2 in
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
                      let uu____5861 =
                        let uu____5870 =
                          FStar_List.tryFind
                            (fun uu____5892  ->
                               match uu____5892 with
                               | (l,uu____5902) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5870 FStar_Util.must in
                      (match uu____5861 with
                       | (uu____5943,op) ->
                           let uu____5953 = op arg_tms1 in
                           (uu____5953, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5964 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5964
       then
         let uu____5965 = FStar_Syntax_Print.tag_of_term t in
         let uu____5966 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5967 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5965 uu____5966
           uu____5967
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5973 ->
           let uu____5998 =
             let uu____5999 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6000 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6001 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6002 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5999
               uu____6000 uu____6001 uu____6002 in
           failwith uu____5998
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6007 =
             let uu____6008 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6009 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6010 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6011 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6008
               uu____6009 uu____6010 uu____6011 in
           failwith uu____6007
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6017 =
             let uu____6018 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6018 in
           failwith uu____6017
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6025) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6066;
              FStar_Syntax_Syntax.vars = uu____6067;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6084 = varops.fresh "t" in
             (uu____6084, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6087 =
               let uu____6098 =
                 let uu____6101 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6101 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6098) in
             FStar_SMTEncoding_Term.DeclFun uu____6087 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6109) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6119 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6119, [])
       | FStar_Syntax_Syntax.Tm_type uu____6122 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6126) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6151 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6151 with
            | (binders1,res) ->
                let uu____6162 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6162
                then
                  let uu____6167 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6167 with
                   | (vars,guards,env',decls,uu____6192) ->
                       let fsym =
                         let uu____6210 = varops.fresh "f" in
                         (uu____6210, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6213 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___334_6222 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___334_6222.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___334_6222.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___334_6222.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___334_6222.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___334_6222.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___334_6222.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___334_6222.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___334_6222.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___334_6222.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___334_6222.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___334_6222.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___334_6222.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___334_6222.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___334_6222.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___334_6222.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___334_6222.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___334_6222.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___334_6222.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___334_6222.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___334_6222.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___334_6222.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___334_6222.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___334_6222.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___334_6222.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___334_6222.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___334_6222.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___334_6222.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___334_6222.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___334_6222.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___334_6222.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___334_6222.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___334_6222.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___334_6222.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6213 with
                        | (pre_opt,res_t) ->
                            let uu____6233 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6233 with
                             | (res_pred,decls') ->
                                 let uu____6244 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6257 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6257, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6261 =
                                         encode_formula pre env' in
                                       (match uu____6261 with
                                        | (guard,decls0) ->
                                            let uu____6274 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6274, decls0)) in
                                 (match uu____6244 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6286 =
                                          let uu____6297 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6297) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6286 in
                                      let cvars =
                                        let uu____6315 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6315
                                          (FStar_List.filter
                                             (fun uu____6329  ->
                                                match uu____6329 with
                                                | (x,uu____6335) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6354 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6354 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6362 =
                                             let uu____6363 =
                                               let uu____6370 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6370) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6363 in
                                           (uu____6362,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6390 =
                                               let uu____6391 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6391 in
                                             varops.mk_unique uu____6390 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6402 =
                                               FStar_Options.log_queries () in
                                             if uu____6402
                                             then
                                               let uu____6405 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6405
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6413 =
                                               let uu____6420 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6420) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6413 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6432 =
                                               let uu____6439 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6439,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6432 in
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
                                             let uu____6460 =
                                               let uu____6467 =
                                                 let uu____6468 =
                                                   let uu____6479 =
                                                     let uu____6480 =
                                                       let uu____6485 =
                                                         let uu____6486 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6486 in
                                                       (f_has_t, uu____6485) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6480 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6479) in
                                                 mkForall_fuel uu____6468 in
                                               (uu____6467,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6460 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6509 =
                                               let uu____6516 =
                                                 let uu____6517 =
                                                   let uu____6528 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6528) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6517 in
                                               (uu____6516,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6509 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6553 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6553);
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
                     let uu____6568 =
                       let uu____6575 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6575,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6568 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6587 =
                       let uu____6594 =
                         let uu____6595 =
                           let uu____6606 =
                             let uu____6607 =
                               let uu____6612 =
                                 let uu____6613 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6613 in
                               (f_has_t, uu____6612) in
                             FStar_SMTEncoding_Util.mkImp uu____6607 in
                           ([[f_has_t]], [fsym], uu____6606) in
                         mkForall_fuel uu____6595 in
                       (uu____6594, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6587 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6640 ->
           let uu____6647 =
             let uu____6652 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6652 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6659;
                 FStar_Syntax_Syntax.vars = uu____6660;_} ->
                 let uu____6667 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6667 with
                  | (b,f1) ->
                      let uu____6692 =
                        let uu____6693 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6693 in
                      (uu____6692, f1))
             | uu____6702 -> failwith "impossible" in
           (match uu____6647 with
            | (x,f) ->
                let uu____6713 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6713 with
                 | (base_t,decls) ->
                     let uu____6724 = gen_term_var env x in
                     (match uu____6724 with
                      | (x1,xtm,env') ->
                          let uu____6738 = encode_formula f env' in
                          (match uu____6738 with
                           | (refinement,decls') ->
                               let uu____6749 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6749 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6765 =
                                        let uu____6768 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6775 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6768
                                          uu____6775 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6765 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6808  ->
                                              match uu____6808 with
                                              | (y,uu____6814) ->
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
                                    let uu____6847 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6847 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6855 =
                                           let uu____6856 =
                                             let uu____6863 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6863) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6856 in
                                         (uu____6855,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6884 =
                                             let uu____6885 =
                                               let uu____6886 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6886 in
                                             Prims.strcat module_name
                                               uu____6885 in
                                           varops.mk_unique uu____6884 in
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
                                           let uu____6900 =
                                             let uu____6907 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6907) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6900 in
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
                                           let uu____6922 =
                                             let uu____6929 =
                                               let uu____6930 =
                                                 let uu____6941 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6941) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6930 in
                                             (uu____6929,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6922 in
                                         let t_kinding =
                                           let uu____6959 =
                                             let uu____6966 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6966,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6959 in
                                         let t_interp =
                                           let uu____6984 =
                                             let uu____6991 =
                                               let uu____6992 =
                                                 let uu____7003 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7003) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6992 in
                                             let uu____7026 =
                                               let uu____7029 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7029 in
                                             (uu____6991, uu____7026,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6984 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7036 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7036);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7066 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7066 in
           let uu____7067 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7067 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7079 =
                    let uu____7086 =
                      let uu____7087 =
                        let uu____7088 =
                          let uu____7089 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7089 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7088 in
                      varops.mk_unique uu____7087 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7086) in
                  FStar_SMTEncoding_Util.mkAssume uu____7079 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7094 ->
           let uu____7109 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7109 with
            | (head1,args_e) ->
                let uu____7150 =
                  let uu____7163 =
                    let uu____7164 = FStar_Syntax_Subst.compress head1 in
                    uu____7164.FStar_Syntax_Syntax.n in
                  (uu____7163, args_e) in
                (match uu____7150 with
                 | uu____7179 when head_redex env head1 ->
                     let uu____7192 = whnf env t in
                     encode_term uu____7192 env
                 | uu____7193 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7212 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7226;
                       FStar_Syntax_Syntax.vars = uu____7227;_},uu____7228),uu____7229::
                    (v1,uu____7231)::(v2,uu____7233)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7284 = encode_term v1 env in
                     (match uu____7284 with
                      | (v11,decls1) ->
                          let uu____7295 = encode_term v2 env in
                          (match uu____7295 with
                           | (v21,decls2) ->
                               let uu____7306 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7306,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7310::(v1,uu____7312)::(v2,uu____7314)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7361 = encode_term v1 env in
                     (match uu____7361 with
                      | (v11,decls1) ->
                          let uu____7372 = encode_term v2 env in
                          (match uu____7372 with
                           | (v21,decls2) ->
                               let uu____7383 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7383,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7387)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7413)::(arg,uu____7415)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7450) ->
                     let e0 =
                       let uu____7468 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7468 in
                     ((let uu____7476 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7476
                       then
                         let uu____7477 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7477
                       else ());
                      (let e =
                         let uu____7482 =
                           let uu____7483 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7484 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7483
                             uu____7484 in
                         uu____7482 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7493),(arg,uu____7495)::[]) -> encode_term arg env
                 | uu____7520 ->
                     let uu____7533 = encode_args args_e env in
                     (match uu____7533 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7588 = encode_term head1 env in
                            match uu____7588 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7652 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7652 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7730  ->
                                                 fun uu____7731  ->
                                                   match (uu____7730,
                                                           uu____7731)
                                                   with
                                                   | ((bv,uu____7753),
                                                      (a,uu____7755)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7773 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7773
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7778 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7778 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7793 =
                                                   let uu____7800 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7809 =
                                                     let uu____7810 =
                                                       let uu____7811 =
                                                         let uu____7812 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7812 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7811 in
                                                     varops.mk_unique
                                                       uu____7810 in
                                                   (uu____7800,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7809) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7793 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7829 = lookup_free_var_sym env fv in
                            match uu____7829 with
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
                                   FStar_Syntax_Syntax.pos = uu____7860;
                                   FStar_Syntax_Syntax.vars = uu____7861;_},uu____7862)
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
                                   FStar_Syntax_Syntax.pos = uu____7873;
                                   FStar_Syntax_Syntax.vars = uu____7874;_},uu____7875)
                                ->
                                let uu____7880 =
                                  let uu____7881 =
                                    let uu____7886 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7886
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7881
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7880
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7916 =
                                  let uu____7917 =
                                    let uu____7922 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7922
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7917
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7916
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7951,(FStar_Util.Inl t1,uu____7953),uu____7954)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8003,(FStar_Util.Inr c,uu____8005),uu____8006)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8055 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8082 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8082 in
                               let uu____8083 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8083 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8099;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8100;_},uu____8101)
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
                                     | uu____8115 ->
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
           let uu____8164 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8164 with
            | (bs1,body1,opening) ->
                let fallback uu____8187 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8194 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8194, [decl]) in
                let is_impure rc =
                  let uu____8201 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8201 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8211 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8211
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8231 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8231
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8235 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8235)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8242 =
                         let uu____8243 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8243 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8242);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8245 =
                       (is_impure rc) &&
                         (let uu____8247 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8247) in
                     if uu____8245
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8254 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8254 with
                        | (vars,guards,envbody,decls,uu____8279) ->
                            let body2 =
                              let uu____8293 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8293
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8295 = encode_term body2 envbody in
                            (match uu____8295 with
                             | (body3,decls') ->
                                 let uu____8306 =
                                   let uu____8315 = codomain_eff rc in
                                   match uu____8315 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8334 = encode_term tfun env in
                                       (match uu____8334 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8306 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8366 =
                                          let uu____8377 =
                                            let uu____8378 =
                                              let uu____8383 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8383, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8378 in
                                          ([], vars, uu____8377) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8366 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8395 =
                                              let uu____8398 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8398
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8395 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8417 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8417 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8425 =
                                             let uu____8426 =
                                               let uu____8433 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8433) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8426 in
                                           (uu____8425,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8444 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8444 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8455 =
                                                    let uu____8456 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8456 = cache_size in
                                                  if uu____8455
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
                                                    let uu____8472 =
                                                      let uu____8473 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8473 in
                                                    varops.mk_unique
                                                      uu____8472 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8480 =
                                                    let uu____8487 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8487) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8480 in
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
                                                      let uu____8505 =
                                                        let uu____8506 =
                                                          let uu____8513 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8513,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8506 in
                                                      [uu____8505] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8526 =
                                                    let uu____8533 =
                                                      let uu____8534 =
                                                        let uu____8545 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8545) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8534 in
                                                    (uu____8533,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8526 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8562 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8562);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8565,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8566;
                          FStar_Syntax_Syntax.lbunivs = uu____8567;
                          FStar_Syntax_Syntax.lbtyp = uu____8568;
                          FStar_Syntax_Syntax.lbeff = uu____8569;
                          FStar_Syntax_Syntax.lbdef = uu____8570;_}::uu____8571),uu____8572)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8598;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8600;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8621 ->
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
              let uu____8691 = encode_term e1 env in
              match uu____8691 with
              | (ee1,decls1) ->
                  let uu____8702 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8702 with
                   | (xs,e21) ->
                       let uu____8727 = FStar_List.hd xs in
                       (match uu____8727 with
                        | (x1,uu____8741) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8743 = encode_body e21 env' in
                            (match uu____8743 with
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
            let uu____8775 =
              let uu____8782 =
                let uu____8783 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8783 in
              gen_term_var env uu____8782 in
            match uu____8775 with
            | (scrsym,scr',env1) ->
                let uu____8791 = encode_term e env1 in
                (match uu____8791 with
                 | (scr,decls) ->
                     let uu____8802 =
                       let encode_branch b uu____8827 =
                         match uu____8827 with
                         | (else_case,decls1) ->
                             let uu____8846 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8846 with
                              | (p,w,br) ->
                                  let uu____8872 = encode_pat env1 p in
                                  (match uu____8872 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8909  ->
                                                   match uu____8909 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8916 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8938 =
                                               encode_term w1 env2 in
                                             (match uu____8938 with
                                              | (w2,decls2) ->
                                                  let uu____8951 =
                                                    let uu____8952 =
                                                      let uu____8957 =
                                                        let uu____8958 =
                                                          let uu____8963 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8963) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8958 in
                                                      (guard, uu____8957) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8952 in
                                                  (uu____8951, decls2)) in
                                       (match uu____8916 with
                                        | (guard1,decls2) ->
                                            let uu____8976 =
                                              encode_br br env2 in
                                            (match uu____8976 with
                                             | (br1,decls3) ->
                                                 let uu____8989 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8989,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8802 with
                      | (match_tm,decls1) ->
                          let uu____9008 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9008, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9048 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9048
       then
         let uu____9049 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9049
       else ());
      (let uu____9051 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9051 with
       | (vars,pat_term) ->
           let uu____9068 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9121  ->
                     fun v1  ->
                       match uu____9121 with
                       | (env1,vars1) ->
                           let uu____9173 = gen_term_var env1 v1 in
                           (match uu____9173 with
                            | (xx,uu____9195,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9068 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9274 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9275 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9276 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9284 = encode_const c env1 in
                      (match uu____9284 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9298::uu____9299 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9302 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9325 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9325 with
                        | (uu____9332,uu____9333::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9336 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9369  ->
                                  match uu____9369 with
                                  | (arg,uu____9377) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9383 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9383)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9410) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9441 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9464 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9508  ->
                                  match uu____9508 with
                                  | (arg,uu____9522) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9528 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9528)) in
                      FStar_All.pipe_right uu____9464 FStar_List.flatten in
                let pat_term1 uu____9556 = encode_term pat_term env1 in
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
      let uu____9566 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9604  ->
                fun uu____9605  ->
                  match (uu____9604, uu____9605) with
                  | ((tms,decls),(t,uu____9641)) ->
                      let uu____9662 = encode_term t env in
                      (match uu____9662 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9566 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9719 = FStar_Syntax_Util.list_elements e in
        match uu____9719 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9740 =
          let uu____9755 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9755 FStar_Syntax_Util.head_and_args in
        match uu____9740 with
        | (head1,args) ->
            let uu____9794 =
              let uu____9807 =
                let uu____9808 = FStar_Syntax_Util.un_uinst head1 in
                uu____9808.FStar_Syntax_Syntax.n in
              (uu____9807, args) in
            (match uu____9794 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9822,uu____9823)::(e,uu____9825)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9860 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9896 =
            let uu____9911 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9911 FStar_Syntax_Util.head_and_args in
          match uu____9896 with
          | (head1,args) ->
              let uu____9952 =
                let uu____9965 =
                  let uu____9966 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9966.FStar_Syntax_Syntax.n in
                (uu____9965, args) in
              (match uu____9952 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9983)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10010 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10032 = smt_pat_or1 t1 in
            (match uu____10032 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10048 = list_elements1 e in
                 FStar_All.pipe_right uu____10048
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10066 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10066
                           (FStar_List.map one_pat)))
             | uu____10077 ->
                 let uu____10082 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10082])
        | uu____10103 ->
            let uu____10106 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10106] in
      let uu____10127 =
        let uu____10146 =
          let uu____10147 = FStar_Syntax_Subst.compress t in
          uu____10147.FStar_Syntax_Syntax.n in
        match uu____10146 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10186 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10186 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10229;
                        FStar_Syntax_Syntax.effect_name = uu____10230;
                        FStar_Syntax_Syntax.result_typ = uu____10231;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10233)::(post,uu____10235)::(pats,uu____10237)::[];
                        FStar_Syntax_Syntax.flags = uu____10238;_}
                      ->
                      let uu____10279 = lemma_pats pats in
                      (binders1, pre, post, uu____10279)
                  | uu____10296 -> failwith "impos"))
        | uu____10315 -> failwith "Impos" in
      match uu____10127 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___335_10363 = env in
            {
              bindings = (uu___335_10363.bindings);
              depth = (uu___335_10363.depth);
              tcenv = (uu___335_10363.tcenv);
              warn = (uu___335_10363.warn);
              cache = (uu___335_10363.cache);
              nolabels = (uu___335_10363.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___335_10363.encode_non_total_function_typ);
              current_module_name = (uu___335_10363.current_module_name)
            } in
          let uu____10364 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10364 with
           | (vars,guards,env2,decls,uu____10389) ->
               let uu____10402 =
                 let uu____10415 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10459 =
                             let uu____10468 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10468
                               FStar_List.unzip in
                           match uu____10459 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10415 FStar_List.unzip in
               (match uu____10402 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___336_10580 = env2 in
                      {
                        bindings = (uu___336_10580.bindings);
                        depth = (uu___336_10580.depth);
                        tcenv = (uu___336_10580.tcenv);
                        warn = (uu___336_10580.warn);
                        cache = (uu___336_10580.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___336_10580.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___336_10580.encode_non_total_function_typ);
                        current_module_name =
                          (uu___336_10580.current_module_name)
                      } in
                    let uu____10581 =
                      let uu____10586 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10586 env3 in
                    (match uu____10581 with
                     | (pre1,decls'') ->
                         let uu____10593 =
                           let uu____10598 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10598 env3 in
                         (match uu____10593 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10608 =
                                let uu____10609 =
                                  let uu____10620 =
                                    let uu____10621 =
                                      let uu____10626 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10626, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10621 in
                                  (pats, vars, uu____10620) in
                                FStar_SMTEncoding_Util.mkForall uu____10609 in
                              (uu____10608, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10645 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10645
        then
          let uu____10646 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10647 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10646 uu____10647
        else () in
      let enc f r l =
        let uu____10680 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10708 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10708 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10680 with
        | (decls,args) ->
            let uu____10737 =
              let uu___337_10738 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___337_10738.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___337_10738.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10737, decls) in
      let const_op f r uu____10769 =
        let uu____10782 = f r in (uu____10782, []) in
      let un_op f l =
        let uu____10801 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10801 in
      let bin_op f uu___311_10817 =
        match uu___311_10817 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10828 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10862 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10885  ->
                 match uu____10885 with
                 | (t,uu____10899) ->
                     let uu____10900 = encode_formula t env in
                     (match uu____10900 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10862 with
        | (decls,phis) ->
            let uu____10929 =
              let uu___338_10930 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___338_10930.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___338_10930.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10929, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10991  ->
               match uu____10991 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11010) -> false
                    | uu____11011 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11026 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11026
        else
          (let uu____11040 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11040 r rf) in
      let mk_imp1 r uu___312_11065 =
        match uu___312_11065 with
        | (lhs,uu____11071)::(rhs,uu____11073)::[] ->
            let uu____11100 = encode_formula rhs env in
            (match uu____11100 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11115) ->
                      (l1, decls1)
                  | uu____11120 ->
                      let uu____11121 = encode_formula lhs env in
                      (match uu____11121 with
                       | (l2,decls2) ->
                           let uu____11132 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11132, (FStar_List.append decls1 decls2)))))
        | uu____11135 -> failwith "impossible" in
      let mk_ite r uu___313_11156 =
        match uu___313_11156 with
        | (guard,uu____11162)::(_then,uu____11164)::(_else,uu____11166)::[]
            ->
            let uu____11203 = encode_formula guard env in
            (match uu____11203 with
             | (g,decls1) ->
                 let uu____11214 = encode_formula _then env in
                 (match uu____11214 with
                  | (t,decls2) ->
                      let uu____11225 = encode_formula _else env in
                      (match uu____11225 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11239 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11264 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11264 in
      let connectives =
        let uu____11282 =
          let uu____11295 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11295) in
        let uu____11312 =
          let uu____11327 =
            let uu____11340 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11340) in
          let uu____11357 =
            let uu____11372 =
              let uu____11387 =
                let uu____11400 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11400) in
              let uu____11417 =
                let uu____11432 =
                  let uu____11447 =
                    let uu____11460 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11460) in
                  [uu____11447;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11432 in
              uu____11387 :: uu____11417 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11372 in
          uu____11327 :: uu____11357 in
        uu____11282 :: uu____11312 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11781 = encode_formula phi' env in
            (match uu____11781 with
             | (phi2,decls) ->
                 let uu____11792 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11792, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11793 ->
            let uu____11800 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11800 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11839 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11839 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11851;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11853;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11874 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11874 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11921::(x,uu____11923)::(t,uu____11925)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11972 = encode_term x env in
                 (match uu____11972 with
                  | (x1,decls) ->
                      let uu____11983 = encode_term t env in
                      (match uu____11983 with
                       | (t1,decls') ->
                           let uu____11994 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11994, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11999)::(msg,uu____12001)::(phi2,uu____12003)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12048 =
                   let uu____12053 =
                     let uu____12054 = FStar_Syntax_Subst.compress r in
                     uu____12054.FStar_Syntax_Syntax.n in
                   let uu____12057 =
                     let uu____12058 = FStar_Syntax_Subst.compress msg in
                     uu____12058.FStar_Syntax_Syntax.n in
                   (uu____12053, uu____12057) in
                 (match uu____12048 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12067))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12073 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12080)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.squash_lid
                 -> encode_formula t env
             | uu____12105 when head_redex env head2 ->
                 let uu____12118 = whnf env phi1 in
                 encode_formula uu____12118 env
             | uu____12119 ->
                 let uu____12132 = encode_term phi1 env in
                 (match uu____12132 with
                  | (tt,decls) ->
                      let uu____12143 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___339_12146 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___339_12146.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___339_12146.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12143, decls)))
        | uu____12147 ->
            let uu____12148 = encode_term phi1 env in
            (match uu____12148 with
             | (tt,decls) ->
                 let uu____12159 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___340_12162 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___340_12162.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___340_12162.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12159, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12198 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12198 with
        | (vars,guards,env2,decls,uu____12237) ->
            let uu____12250 =
              let uu____12263 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12311 =
                          let uu____12320 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12350  ->
                                    match uu____12350 with
                                    | (t,uu____12360) ->
                                        encode_term t
                                          (let uu___341_12362 = env2 in
                                           {
                                             bindings =
                                               (uu___341_12362.bindings);
                                             depth = (uu___341_12362.depth);
                                             tcenv = (uu___341_12362.tcenv);
                                             warn = (uu___341_12362.warn);
                                             cache = (uu___341_12362.cache);
                                             nolabels =
                                               (uu___341_12362.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___341_12362.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___341_12362.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12320 FStar_List.unzip in
                        match uu____12311 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12263 FStar_List.unzip in
            (match uu____12250 with
             | (pats,decls') ->
                 let uu____12461 = encode_formula body env2 in
                 (match uu____12461 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12493;
                             FStar_SMTEncoding_Term.rng = uu____12494;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12509 -> guards in
                      let uu____12514 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12514, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12574  ->
                   match uu____12574 with
                   | (x,uu____12580) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12588 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12600 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12600) uu____12588 tl1 in
             let uu____12603 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12630  ->
                       match uu____12630 with
                       | (b,uu____12636) ->
                           let uu____12637 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12637)) in
             (match uu____12603 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12643) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12657 =
                    let uu____12658 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12658 in
                  FStar_Errors.warn pos uu____12657) in
       let uu____12659 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12659 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12668 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12726  ->
                     match uu____12726 with
                     | (l,uu____12740) -> FStar_Ident.lid_equals op l)) in
           (match uu____12668 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12773,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12813 = encode_q_body env vars pats body in
             match uu____12813 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12858 =
                     let uu____12869 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12869) in
                   FStar_SMTEncoding_Term.mkForall uu____12858
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12888 = encode_q_body env vars pats body in
             match uu____12888 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12932 =
                   let uu____12933 =
                     let uu____12944 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12944) in
                   FStar_SMTEncoding_Term.mkExists uu____12933
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12932, decls))))
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
  let uu____13037 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13037 with
  | (asym,a) ->
      let uu____13044 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13044 with
       | (xsym,x) ->
           let uu____13051 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13051 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13095 =
                      let uu____13106 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13106, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13095 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13132 =
                      let uu____13139 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13139) in
                    FStar_SMTEncoding_Util.mkApp uu____13132 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13152 =
                    let uu____13155 =
                      let uu____13158 =
                        let uu____13161 =
                          let uu____13162 =
                            let uu____13169 =
                              let uu____13170 =
                                let uu____13181 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13181) in
                              FStar_SMTEncoding_Util.mkForall uu____13170 in
                            (uu____13169, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13162 in
                        let uu____13198 =
                          let uu____13201 =
                            let uu____13202 =
                              let uu____13209 =
                                let uu____13210 =
                                  let uu____13221 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13221) in
                                FStar_SMTEncoding_Util.mkForall uu____13210 in
                              (uu____13209,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13202 in
                          [uu____13201] in
                        uu____13161 :: uu____13198 in
                      xtok_decl :: uu____13158 in
                    xname_decl :: uu____13155 in
                  (xtok1, uu____13152) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13312 =
                    let uu____13325 =
                      let uu____13334 =
                        let uu____13335 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13335 in
                      quant axy uu____13334 in
                    (FStar_Parser_Const.op_Eq, uu____13325) in
                  let uu____13344 =
                    let uu____13359 =
                      let uu____13372 =
                        let uu____13381 =
                          let uu____13382 =
                            let uu____13383 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13383 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13382 in
                        quant axy uu____13381 in
                      (FStar_Parser_Const.op_notEq, uu____13372) in
                    let uu____13392 =
                      let uu____13407 =
                        let uu____13420 =
                          let uu____13429 =
                            let uu____13430 =
                              let uu____13431 =
                                let uu____13436 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13437 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13436, uu____13437) in
                              FStar_SMTEncoding_Util.mkLT uu____13431 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13430 in
                          quant xy uu____13429 in
                        (FStar_Parser_Const.op_LT, uu____13420) in
                      let uu____13446 =
                        let uu____13461 =
                          let uu____13474 =
                            let uu____13483 =
                              let uu____13484 =
                                let uu____13485 =
                                  let uu____13490 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13491 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13490, uu____13491) in
                                FStar_SMTEncoding_Util.mkLTE uu____13485 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13484 in
                            quant xy uu____13483 in
                          (FStar_Parser_Const.op_LTE, uu____13474) in
                        let uu____13500 =
                          let uu____13515 =
                            let uu____13528 =
                              let uu____13537 =
                                let uu____13538 =
                                  let uu____13539 =
                                    let uu____13544 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13545 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13544, uu____13545) in
                                  FStar_SMTEncoding_Util.mkGT uu____13539 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13538 in
                              quant xy uu____13537 in
                            (FStar_Parser_Const.op_GT, uu____13528) in
                          let uu____13554 =
                            let uu____13569 =
                              let uu____13582 =
                                let uu____13591 =
                                  let uu____13592 =
                                    let uu____13593 =
                                      let uu____13598 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13599 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13598, uu____13599) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13593 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13592 in
                                quant xy uu____13591 in
                              (FStar_Parser_Const.op_GTE, uu____13582) in
                            let uu____13608 =
                              let uu____13623 =
                                let uu____13636 =
                                  let uu____13645 =
                                    let uu____13646 =
                                      let uu____13647 =
                                        let uu____13652 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13653 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13652, uu____13653) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13647 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13646 in
                                  quant xy uu____13645 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13636) in
                              let uu____13662 =
                                let uu____13677 =
                                  let uu____13690 =
                                    let uu____13699 =
                                      let uu____13700 =
                                        let uu____13701 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13701 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13700 in
                                    quant qx uu____13699 in
                                  (FStar_Parser_Const.op_Minus, uu____13690) in
                                let uu____13710 =
                                  let uu____13725 =
                                    let uu____13738 =
                                      let uu____13747 =
                                        let uu____13748 =
                                          let uu____13749 =
                                            let uu____13754 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13755 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13754, uu____13755) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13749 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13748 in
                                      quant xy uu____13747 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13738) in
                                  let uu____13764 =
                                    let uu____13779 =
                                      let uu____13792 =
                                        let uu____13801 =
                                          let uu____13802 =
                                            let uu____13803 =
                                              let uu____13808 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13809 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13808, uu____13809) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13803 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13802 in
                                        quant xy uu____13801 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13792) in
                                    let uu____13818 =
                                      let uu____13833 =
                                        let uu____13846 =
                                          let uu____13855 =
                                            let uu____13856 =
                                              let uu____13857 =
                                                let uu____13862 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13863 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13862, uu____13863) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13857 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13856 in
                                          quant xy uu____13855 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13846) in
                                      let uu____13872 =
                                        let uu____13887 =
                                          let uu____13900 =
                                            let uu____13909 =
                                              let uu____13910 =
                                                let uu____13911 =
                                                  let uu____13916 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13917 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13916, uu____13917) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13911 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13910 in
                                            quant xy uu____13909 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13900) in
                                        let uu____13926 =
                                          let uu____13941 =
                                            let uu____13954 =
                                              let uu____13963 =
                                                let uu____13964 =
                                                  let uu____13965 =
                                                    let uu____13970 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13971 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13970,
                                                      uu____13971) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13965 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13964 in
                                              quant xy uu____13963 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13954) in
                                          let uu____13980 =
                                            let uu____13995 =
                                              let uu____14008 =
                                                let uu____14017 =
                                                  let uu____14018 =
                                                    let uu____14019 =
                                                      let uu____14024 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14025 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14024,
                                                        uu____14025) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14019 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14018 in
                                                quant xy uu____14017 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14008) in
                                            let uu____14034 =
                                              let uu____14049 =
                                                let uu____14062 =
                                                  let uu____14071 =
                                                    let uu____14072 =
                                                      let uu____14073 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14073 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14072 in
                                                  quant qx uu____14071 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14062) in
                                              [uu____14049] in
                                            uu____13995 :: uu____14034 in
                                          uu____13941 :: uu____13980 in
                                        uu____13887 :: uu____13926 in
                                      uu____13833 :: uu____13872 in
                                    uu____13779 :: uu____13818 in
                                  uu____13725 :: uu____13764 in
                                uu____13677 :: uu____13710 in
                              uu____13623 :: uu____13662 in
                            uu____13569 :: uu____13608 in
                          uu____13515 :: uu____13554 in
                        uu____13461 :: uu____13500 in
                      uu____13407 :: uu____13446 in
                    uu____13359 :: uu____13392 in
                  uu____13312 :: uu____13344 in
                let mk1 l v1 =
                  let uu____14287 =
                    let uu____14296 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14354  ->
                              match uu____14354 with
                              | (l',uu____14368) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14296
                      (FStar_Option.map
                         (fun uu____14428  ->
                            match uu____14428 with | (uu____14447,b) -> b v1)) in
                  FStar_All.pipe_right uu____14287 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14518  ->
                          match uu____14518 with
                          | (l',uu____14532) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14570 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14570 with
        | (xxsym,xx) ->
            let uu____14577 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14577 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14587 =
                   let uu____14594 =
                     let uu____14595 =
                       let uu____14606 =
                         let uu____14607 =
                           let uu____14612 =
                             let uu____14613 =
                               let uu____14618 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14618) in
                             FStar_SMTEncoding_Util.mkEq uu____14613 in
                           (xx_has_type, uu____14612) in
                         FStar_SMTEncoding_Util.mkImp uu____14607 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14606) in
                     FStar_SMTEncoding_Util.mkForall uu____14595 in
                   let uu____14643 =
                     let uu____14644 =
                       let uu____14645 =
                         let uu____14646 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14646 in
                       Prims.strcat module_name uu____14645 in
                     varops.mk_unique uu____14644 in
                   (uu____14594, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14643) in
                 FStar_SMTEncoding_Util.mkAssume uu____14587)
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
    let uu____14682 =
      let uu____14683 =
        let uu____14690 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14690, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14683 in
    let uu____14693 =
      let uu____14696 =
        let uu____14697 =
          let uu____14704 =
            let uu____14705 =
              let uu____14716 =
                let uu____14717 =
                  let uu____14722 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14722) in
                FStar_SMTEncoding_Util.mkImp uu____14717 in
              ([[typing_pred]], [xx], uu____14716) in
            mkForall_fuel uu____14705 in
          (uu____14704, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14697 in
      [uu____14696] in
    uu____14682 :: uu____14693 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14764 =
      let uu____14765 =
        let uu____14772 =
          let uu____14773 =
            let uu____14784 =
              let uu____14789 =
                let uu____14792 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14792] in
              [uu____14789] in
            let uu____14797 =
              let uu____14798 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14798 tt in
            (uu____14784, [bb], uu____14797) in
          FStar_SMTEncoding_Util.mkForall uu____14773 in
        (uu____14772, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14765 in
    let uu____14819 =
      let uu____14822 =
        let uu____14823 =
          let uu____14830 =
            let uu____14831 =
              let uu____14842 =
                let uu____14843 =
                  let uu____14848 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14848) in
                FStar_SMTEncoding_Util.mkImp uu____14843 in
              ([[typing_pred]], [xx], uu____14842) in
            mkForall_fuel uu____14831 in
          (uu____14830, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14823 in
      [uu____14822] in
    uu____14764 :: uu____14819 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14898 =
        let uu____14899 =
          let uu____14906 =
            let uu____14909 =
              let uu____14912 =
                let uu____14915 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14916 =
                  let uu____14919 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14919] in
                uu____14915 :: uu____14916 in
              tt :: uu____14912 in
            tt :: uu____14909 in
          ("Prims.Precedes", uu____14906) in
        FStar_SMTEncoding_Util.mkApp uu____14899 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14898 in
    let precedes_y_x =
      let uu____14923 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14923 in
    let uu____14926 =
      let uu____14927 =
        let uu____14934 =
          let uu____14935 =
            let uu____14946 =
              let uu____14951 =
                let uu____14954 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14954] in
              [uu____14951] in
            let uu____14959 =
              let uu____14960 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14960 tt in
            (uu____14946, [bb], uu____14959) in
          FStar_SMTEncoding_Util.mkForall uu____14935 in
        (uu____14934, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14927 in
    let uu____14981 =
      let uu____14984 =
        let uu____14985 =
          let uu____14992 =
            let uu____14993 =
              let uu____15004 =
                let uu____15005 =
                  let uu____15010 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15010) in
                FStar_SMTEncoding_Util.mkImp uu____15005 in
              ([[typing_pred]], [xx], uu____15004) in
            mkForall_fuel uu____14993 in
          (uu____14992, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14985 in
      let uu____15035 =
        let uu____15038 =
          let uu____15039 =
            let uu____15046 =
              let uu____15047 =
                let uu____15058 =
                  let uu____15059 =
                    let uu____15064 =
                      let uu____15065 =
                        let uu____15068 =
                          let uu____15071 =
                            let uu____15074 =
                              let uu____15075 =
                                let uu____15080 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15081 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15080, uu____15081) in
                              FStar_SMTEncoding_Util.mkGT uu____15075 in
                            let uu____15082 =
                              let uu____15085 =
                                let uu____15086 =
                                  let uu____15091 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15092 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15091, uu____15092) in
                                FStar_SMTEncoding_Util.mkGTE uu____15086 in
                              let uu____15093 =
                                let uu____15096 =
                                  let uu____15097 =
                                    let uu____15102 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15103 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15102, uu____15103) in
                                  FStar_SMTEncoding_Util.mkLT uu____15097 in
                                [uu____15096] in
                              uu____15085 :: uu____15093 in
                            uu____15074 :: uu____15082 in
                          typing_pred_y :: uu____15071 in
                        typing_pred :: uu____15068 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15065 in
                    (uu____15064, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15059 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15058) in
              mkForall_fuel uu____15047 in
            (uu____15046,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15039 in
        [uu____15038] in
      uu____14984 :: uu____15035 in
    uu____14926 :: uu____14981 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15149 =
      let uu____15150 =
        let uu____15157 =
          let uu____15158 =
            let uu____15169 =
              let uu____15174 =
                let uu____15177 = FStar_SMTEncoding_Term.boxString b in
                [uu____15177] in
              [uu____15174] in
            let uu____15182 =
              let uu____15183 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15183 tt in
            (uu____15169, [bb], uu____15182) in
          FStar_SMTEncoding_Util.mkForall uu____15158 in
        (uu____15157, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15150 in
    let uu____15204 =
      let uu____15207 =
        let uu____15208 =
          let uu____15215 =
            let uu____15216 =
              let uu____15227 =
                let uu____15228 =
                  let uu____15233 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15233) in
                FStar_SMTEncoding_Util.mkImp uu____15228 in
              ([[typing_pred]], [xx], uu____15227) in
            mkForall_fuel uu____15216 in
          (uu____15215, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15208 in
      [uu____15207] in
    uu____15149 :: uu____15204 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15286 =
      let uu____15287 =
        let uu____15294 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15294, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15287 in
    [uu____15286] in
  let mk_and_interp env conj uu____15306 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15331 =
      let uu____15332 =
        let uu____15339 =
          let uu____15340 =
            let uu____15351 =
              let uu____15352 =
                let uu____15357 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15357, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15352 in
            ([[l_and_a_b]], [aa; bb], uu____15351) in
          FStar_SMTEncoding_Util.mkForall uu____15340 in
        (uu____15339, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15332 in
    [uu____15331] in
  let mk_or_interp env disj uu____15395 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15420 =
      let uu____15421 =
        let uu____15428 =
          let uu____15429 =
            let uu____15440 =
              let uu____15441 =
                let uu____15446 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15446, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15441 in
            ([[l_or_a_b]], [aa; bb], uu____15440) in
          FStar_SMTEncoding_Util.mkForall uu____15429 in
        (uu____15428, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15421 in
    [uu____15420] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15509 =
      let uu____15510 =
        let uu____15517 =
          let uu____15518 =
            let uu____15529 =
              let uu____15530 =
                let uu____15535 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15535, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15530 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15529) in
          FStar_SMTEncoding_Util.mkForall uu____15518 in
        (uu____15517, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15510 in
    [uu____15509] in
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
    let uu____15608 =
      let uu____15609 =
        let uu____15616 =
          let uu____15617 =
            let uu____15628 =
              let uu____15629 =
                let uu____15634 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15634, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15629 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15628) in
          FStar_SMTEncoding_Util.mkForall uu____15617 in
        (uu____15616, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15609 in
    [uu____15608] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15705 =
      let uu____15706 =
        let uu____15713 =
          let uu____15714 =
            let uu____15725 =
              let uu____15726 =
                let uu____15731 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15731, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15726 in
            ([[l_imp_a_b]], [aa; bb], uu____15725) in
          FStar_SMTEncoding_Util.mkForall uu____15714 in
        (uu____15713, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15706 in
    [uu____15705] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15794 =
      let uu____15795 =
        let uu____15802 =
          let uu____15803 =
            let uu____15814 =
              let uu____15815 =
                let uu____15820 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15820, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15815 in
            ([[l_iff_a_b]], [aa; bb], uu____15814) in
          FStar_SMTEncoding_Util.mkForall uu____15803 in
        (uu____15802, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15795 in
    [uu____15794] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15872 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15872 in
    let uu____15875 =
      let uu____15876 =
        let uu____15883 =
          let uu____15884 =
            let uu____15895 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15895) in
          FStar_SMTEncoding_Util.mkForall uu____15884 in
        (uu____15883, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15876 in
    [uu____15875] in
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
      let uu____15955 =
        let uu____15962 =
          let uu____15965 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15965] in
        ("Valid", uu____15962) in
      FStar_SMTEncoding_Util.mkApp uu____15955 in
    let uu____15968 =
      let uu____15969 =
        let uu____15976 =
          let uu____15977 =
            let uu____15988 =
              let uu____15989 =
                let uu____15994 =
                  let uu____15995 =
                    let uu____16006 =
                      let uu____16011 =
                        let uu____16014 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16014] in
                      [uu____16011] in
                    let uu____16019 =
                      let uu____16020 =
                        let uu____16025 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16025, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16020 in
                    (uu____16006, [xx1], uu____16019) in
                  FStar_SMTEncoding_Util.mkForall uu____15995 in
                (uu____15994, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15989 in
            ([[l_forall_a_b]], [aa; bb], uu____15988) in
          FStar_SMTEncoding_Util.mkForall uu____15977 in
        (uu____15976, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15969 in
    [uu____15968] in
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
      let uu____16107 =
        let uu____16114 =
          let uu____16117 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16117] in
        ("Valid", uu____16114) in
      FStar_SMTEncoding_Util.mkApp uu____16107 in
    let uu____16120 =
      let uu____16121 =
        let uu____16128 =
          let uu____16129 =
            let uu____16140 =
              let uu____16141 =
                let uu____16146 =
                  let uu____16147 =
                    let uu____16158 =
                      let uu____16163 =
                        let uu____16166 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16166] in
                      [uu____16163] in
                    let uu____16171 =
                      let uu____16172 =
                        let uu____16177 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16177, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16172 in
                    (uu____16158, [xx1], uu____16171) in
                  FStar_SMTEncoding_Util.mkExists uu____16147 in
                (uu____16146, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16141 in
            ([[l_exists_a_b]], [aa; bb], uu____16140) in
          FStar_SMTEncoding_Util.mkForall uu____16129 in
        (uu____16128, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16121 in
    [uu____16120] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16237 =
      let uu____16238 =
        let uu____16245 =
          let uu____16246 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16246 range_ty in
        let uu____16247 = varops.mk_unique "typing_range_const" in
        (uu____16245, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16247) in
      FStar_SMTEncoding_Util.mkAssume uu____16238 in
    [uu____16237] in
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
        let uu____16281 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16281 x1 t in
      let uu____16282 =
        let uu____16293 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16293) in
      FStar_SMTEncoding_Util.mkForall uu____16282 in
    let uu____16316 =
      let uu____16317 =
        let uu____16324 =
          let uu____16325 =
            let uu____16336 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16336) in
          FStar_SMTEncoding_Util.mkForall uu____16325 in
        (uu____16324,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16317 in
    [uu____16316] in
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
          let uu____16660 =
            FStar_Util.find_opt
              (fun uu____16686  ->
                 match uu____16686 with
                 | (l,uu____16698) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16660 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16723,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16759 = encode_function_type_as_formula t env in
        match uu____16759 with
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
              let uu____16799 =
                ((let uu____16802 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16802) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16799
              then
                let uu____16809 = new_term_constant_and_tok_from_lid env lid in
                match uu____16809 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16828 =
                        let uu____16829 = FStar_Syntax_Subst.compress t_norm in
                        uu____16829.FStar_Syntax_Syntax.n in
                      match uu____16828 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16835) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16865  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16870 -> [] in
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
                (let uu____16884 = prims.is lid in
                 if uu____16884
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16892 = prims.mk lid vname in
                   match uu____16892 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16916 =
                      let uu____16927 = curried_arrow_formals_comp t_norm in
                      match uu____16927 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16945 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16945
                            then
                              let uu____16946 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___342_16949 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___342_16949.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___342_16949.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___342_16949.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___342_16949.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___342_16949.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___342_16949.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___342_16949.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___342_16949.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___342_16949.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___342_16949.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___342_16949.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___342_16949.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___342_16949.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___342_16949.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___342_16949.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___342_16949.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___342_16949.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___342_16949.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___342_16949.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___342_16949.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___342_16949.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___342_16949.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___342_16949.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___342_16949.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___342_16949.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___342_16949.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___342_16949.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___342_16949.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___342_16949.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___342_16949.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___342_16949.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___342_16949.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___342_16949.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16946
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16961 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16961)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16916 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17006 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17006 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17027 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___314_17069  ->
                                       match uu___314_17069 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17073 =
                                             FStar_Util.prefix vars in
                                           (match uu____17073 with
                                            | (uu____17094,(xxsym,uu____17096))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17114 =
                                                  let uu____17115 =
                                                    let uu____17122 =
                                                      let uu____17123 =
                                                        let uu____17134 =
                                                          let uu____17135 =
                                                            let uu____17140 =
                                                              let uu____17141
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17141 in
                                                            (vapp,
                                                              uu____17140) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17135 in
                                                        ([[vapp]], vars,
                                                          uu____17134) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17123 in
                                                    (uu____17122,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17115 in
                                                [uu____17114])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17160 =
                                             FStar_Util.prefix vars in
                                           (match uu____17160 with
                                            | (uu____17181,(xxsym,uu____17183))
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
                                                let uu____17206 =
                                                  let uu____17207 =
                                                    let uu____17214 =
                                                      let uu____17215 =
                                                        let uu____17226 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17226) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17215 in
                                                    (uu____17214,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17207 in
                                                [uu____17206])
                                       | uu____17243 -> [])) in
                             let uu____17244 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17244 with
                              | (vars,guards,env',decls1,uu____17271) ->
                                  let uu____17284 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17293 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17293, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17295 =
                                          encode_formula p env' in
                                        (match uu____17295 with
                                         | (g,ds) ->
                                             let uu____17306 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17306,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17284 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17319 =
                                           let uu____17326 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17326) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17319 in
                                       let uu____17335 =
                                         let vname_decl =
                                           let uu____17343 =
                                             let uu____17354 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17364  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17354,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17343 in
                                         let uu____17373 =
                                           let env2 =
                                             let uu___343_17379 = env1 in
                                             {
                                               bindings =
                                                 (uu___343_17379.bindings);
                                               depth = (uu___343_17379.depth);
                                               tcenv = (uu___343_17379.tcenv);
                                               warn = (uu___343_17379.warn);
                                               cache = (uu___343_17379.cache);
                                               nolabels =
                                                 (uu___343_17379.nolabels);
                                               use_zfuel_name =
                                                 (uu___343_17379.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___343_17379.current_module_name)
                                             } in
                                           let uu____17380 =
                                             let uu____17381 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17381 in
                                           if uu____17380
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17373 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17396::uu____17397 ->
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
                                                     let uu____17437 =
                                                       let uu____17448 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17448) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17437 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17475 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17478 =
                                               match formals with
                                               | [] ->
                                                   let uu____17495 =
                                                     let uu____17496 =
                                                       let uu____17499 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17499 in
                                                     push_free_var env1 lid
                                                       vname uu____17496 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17495)
                                               | uu____17504 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17511 =
                                                       let uu____17518 =
                                                         let uu____17519 =
                                                           let uu____17530 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17530) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17519 in
                                                       (uu____17518,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17511 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17478 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17335 with
                                        | (decls2,env2) ->
                                            let uu____17573 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17581 =
                                                encode_term res_t1 env' in
                                              match uu____17581 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17594 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17594, decls) in
                                            (match uu____17573 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17605 =
                                                     let uu____17612 =
                                                       let uu____17613 =
                                                         let uu____17624 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17624) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17613 in
                                                     (uu____17612,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17605 in
                                                 let freshness =
                                                   let uu____17640 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17640
                                                   then
                                                     let uu____17645 =
                                                       let uu____17646 =
                                                         let uu____17657 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17668 =
                                                           varops.next_id () in
                                                         (vname, uu____17657,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17668) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17646 in
                                                     let uu____17671 =
                                                       let uu____17674 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17674] in
                                                     uu____17645 ::
                                                       uu____17671
                                                   else [] in
                                                 let g =
                                                   let uu____17679 =
                                                     let uu____17682 =
                                                       let uu____17685 =
                                                         let uu____17688 =
                                                           let uu____17691 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17691 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17688 in
                                                       FStar_List.append
                                                         decls3 uu____17685 in
                                                     FStar_List.append decls2
                                                       uu____17682 in
                                                   FStar_List.append decls11
                                                     uu____17679 in
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
          let uu____17722 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17722 with
          | FStar_Pervasives_Native.None  ->
              let uu____17759 = encode_free_var false env x t t_norm [] in
              (match uu____17759 with
               | (decls,env1) ->
                   let uu____17786 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17786 with
                    | (n1,x',uu____17813) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17834) ->
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
            let uu____17889 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17889 with
            | (decls,env1) ->
                let uu____17908 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17908
                then
                  let uu____17915 =
                    let uu____17918 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17918 in
                  (uu____17915, env1)
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
             (fun uu____17970  ->
                fun lb  ->
                  match uu____17970 with
                  | (decls,env1) ->
                      let uu____17990 =
                        let uu____17997 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17997
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17990 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18018 = FStar_Syntax_Util.head_and_args t in
    match uu____18018 with
    | (hd1,args) ->
        let uu____18055 =
          let uu____18056 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18056.FStar_Syntax_Syntax.n in
        (match uu____18055 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18060,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18079 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18101  ->
      fun quals  ->
        match uu____18101 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18177 = FStar_Util.first_N nbinders formals in
              match uu____18177 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18258  ->
                         fun uu____18259  ->
                           match (uu____18258, uu____18259) with
                           | ((formal,uu____18277),(binder,uu____18279)) ->
                               let uu____18288 =
                                 let uu____18295 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18295) in
                               FStar_Syntax_Syntax.NT uu____18288) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18303 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18334  ->
                              match uu____18334 with
                              | (x,i) ->
                                  let uu____18345 =
                                    let uu___344_18346 = x in
                                    let uu____18347 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___344_18346.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___344_18346.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18347
                                    } in
                                  (uu____18345, i))) in
                    FStar_All.pipe_right uu____18303
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18365 =
                      let uu____18366 = FStar_Syntax_Subst.compress body in
                      let uu____18367 =
                        let uu____18368 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18368 in
                      FStar_Syntax_Syntax.extend_app_n uu____18366
                        uu____18367 in
                    uu____18365 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18429 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18429
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___345_18432 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___345_18432.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___345_18432.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___345_18432.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___345_18432.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___345_18432.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___345_18432.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___345_18432.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___345_18432.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___345_18432.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___345_18432.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___345_18432.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___345_18432.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___345_18432.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___345_18432.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___345_18432.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___345_18432.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___345_18432.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___345_18432.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___345_18432.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___345_18432.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___345_18432.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___345_18432.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___345_18432.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___345_18432.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___345_18432.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___345_18432.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___345_18432.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___345_18432.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___345_18432.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___345_18432.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___345_18432.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___345_18432.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___345_18432.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18465 = FStar_Syntax_Util.abs_formals e in
                match uu____18465 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18529::uu____18530 ->
                         let uu____18545 =
                           let uu____18546 =
                             let uu____18549 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18549 in
                           uu____18546.FStar_Syntax_Syntax.n in
                         (match uu____18545 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18592 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18592 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18634 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18634
                                   then
                                     let uu____18669 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18669 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18763  ->
                                                   fun uu____18764  ->
                                                     match (uu____18763,
                                                             uu____18764)
                                                     with
                                                     | ((x,uu____18782),
                                                        (b,uu____18784)) ->
                                                         let uu____18793 =
                                                           let uu____18800 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18800) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18793)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18802 =
                                            let uu____18823 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18823) in
                                          (uu____18802, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18891 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18891 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18980) ->
                              let uu____18985 =
                                let uu____19006 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19006 in
                              (uu____18985, true)
                          | uu____19071 when Prims.op_Negation norm1 ->
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
                          | uu____19073 ->
                              let uu____19074 =
                                let uu____19075 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19076 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19075
                                  uu____19076 in
                              failwith uu____19074)
                     | uu____19101 ->
                         let rec aux' t_norm2 =
                           let uu____19126 =
                             let uu____19127 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19127.FStar_Syntax_Syntax.n in
                           match uu____19126 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19168 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19168 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19196 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19196 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19276)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19281 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19337 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19337
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19349 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19443  ->
                            fun lb  ->
                              match uu____19443 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19538 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19538
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19541 =
                                      let uu____19556 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19556
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19541 with
                                    | (tok,decl,env2) ->
                                        let uu____19602 =
                                          let uu____19615 =
                                            let uu____19626 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19626, tok) in
                                          uu____19615 :: toks in
                                        (uu____19602, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19349 with
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
                        | uu____19809 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19817 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19817 vars)
                            else
                              (let uu____19819 =
                                 let uu____19826 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19826) in
                               FStar_SMTEncoding_Util.mkApp uu____19819) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19908;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19910;
                             FStar_Syntax_Syntax.lbeff = uu____19911;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19974 =
                              let uu____19981 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19981 with
                              | (tcenv',uu____19999,e_t) ->
                                  let uu____20005 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20016 -> failwith "Impossible" in
                                  (match uu____20005 with
                                   | (e1,t_norm1) ->
                                       ((let uu___348_20032 = env2 in
                                         {
                                           bindings =
                                             (uu___348_20032.bindings);
                                           depth = (uu___348_20032.depth);
                                           tcenv = tcenv';
                                           warn = (uu___348_20032.warn);
                                           cache = (uu___348_20032.cache);
                                           nolabels =
                                             (uu___348_20032.nolabels);
                                           use_zfuel_name =
                                             (uu___348_20032.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___348_20032.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___348_20032.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19974 with
                             | (env',e1,t_norm1) ->
                                 let uu____20042 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20042 with
                                  | ((binders,body,uu____20063,uu____20064),curry)
                                      ->
                                      ((let uu____20075 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20075
                                        then
                                          let uu____20076 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20077 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20076 uu____20077
                                        else ());
                                       (let uu____20079 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20079 with
                                        | (vars,guards,env'1,binder_decls,uu____20106)
                                            ->
                                            let body1 =
                                              let uu____20120 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20120
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20123 =
                                              let uu____20132 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20132
                                              then
                                                let uu____20143 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20144 =
                                                  encode_formula body1 env'1 in
                                                (uu____20143, uu____20144)
                                              else
                                                (let uu____20154 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20154)) in
                                            (match uu____20123 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20177 =
                                                     let uu____20184 =
                                                       let uu____20185 =
                                                         let uu____20196 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20196) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20185 in
                                                     let uu____20207 =
                                                       let uu____20210 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20210 in
                                                     (uu____20184,
                                                       uu____20207,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20177 in
                                                 let uu____20213 =
                                                   let uu____20216 =
                                                     let uu____20219 =
                                                       let uu____20222 =
                                                         let uu____20225 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20225 in
                                                       FStar_List.append
                                                         decls2 uu____20222 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20219 in
                                                   FStar_List.append decls1
                                                     uu____20216 in
                                                 (uu____20213, env2))))))
                        | uu____20230 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20315 = varops.fresh "fuel" in
                          (uu____20315, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20318 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20406  ->
                                  fun uu____20407  ->
                                    match (uu____20406, uu____20407) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20555 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20555 in
                                        let gtok =
                                          let uu____20557 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20557 in
                                        let env4 =
                                          let uu____20559 =
                                            let uu____20562 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20562 in
                                          push_free_var env3 flid gtok
                                            uu____20559 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20318 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20718 t_norm
                              uu____20720 =
                              match (uu____20718, uu____20720) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20764;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20765;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20793 =
                                    let uu____20800 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20800 with
                                    | (tcenv',uu____20822,e_t) ->
                                        let uu____20828 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20839 ->
                                              failwith "Impossible" in
                                        (match uu____20828 with
                                         | (e1,t_norm1) ->
                                             ((let uu___349_20855 = env3 in
                                               {
                                                 bindings =
                                                   (uu___349_20855.bindings);
                                                 depth =
                                                   (uu___349_20855.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___349_20855.warn);
                                                 cache =
                                                   (uu___349_20855.cache);
                                                 nolabels =
                                                   (uu___349_20855.nolabels);
                                                 use_zfuel_name =
                                                   (uu___349_20855.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___349_20855.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___349_20855.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20793 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20870 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20870
                                         then
                                           let uu____20871 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20872 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20873 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20871 uu____20872
                                             uu____20873
                                         else ());
                                        (let uu____20875 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20875 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20912 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20912
                                               then
                                                 let uu____20913 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20914 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20915 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20916 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20913 uu____20914
                                                   uu____20915 uu____20916
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20920 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20920 with
                                               | (vars,guards,env'1,binder_decls,uu____20951)
                                                   ->
                                                   let decl_g =
                                                     let uu____20965 =
                                                       let uu____20976 =
                                                         let uu____20979 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20979 in
                                                       (g, uu____20976,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20965 in
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
                                                     let uu____21004 =
                                                       let uu____21011 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21011) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21004 in
                                                   let gsapp =
                                                     let uu____21021 =
                                                       let uu____21028 =
                                                         let uu____21031 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21031 ::
                                                           vars_tm in
                                                       (g, uu____21028) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21021 in
                                                   let gmax =
                                                     let uu____21037 =
                                                       let uu____21044 =
                                                         let uu____21047 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21047 ::
                                                           vars_tm in
                                                       (g, uu____21044) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21037 in
                                                   let body1 =
                                                     let uu____21053 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21053
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21055 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21055 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21073 =
                                                            let uu____21080 =
                                                              let uu____21081
                                                                =
                                                                let uu____21096
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
                                                                  uu____21096) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21081 in
                                                            let uu____21117 =
                                                              let uu____21120
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21120 in
                                                            (uu____21080,
                                                              uu____21117,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21073 in
                                                        let eqn_f =
                                                          let uu____21124 =
                                                            let uu____21131 =
                                                              let uu____21132
                                                                =
                                                                let uu____21143
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21143) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21132 in
                                                            (uu____21131,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21124 in
                                                        let eqn_g' =
                                                          let uu____21157 =
                                                            let uu____21164 =
                                                              let uu____21165
                                                                =
                                                                let uu____21176
                                                                  =
                                                                  let uu____21177
                                                                    =
                                                                    let uu____21182
                                                                    =
                                                                    let uu____21183
                                                                    =
                                                                    let uu____21190
                                                                    =
                                                                    let uu____21193
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21193
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21190) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21183 in
                                                                    (gsapp,
                                                                    uu____21182) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21177 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21176) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21165 in
                                                            (uu____21164,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21157 in
                                                        let uu____21216 =
                                                          let uu____21225 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21225
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21254)
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
                                                                  let uu____21279
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21279
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21284
                                                                  =
                                                                  let uu____21291
                                                                    =
                                                                    let uu____21292
                                                                    =
                                                                    let uu____21303
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21303) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21292 in
                                                                  (uu____21291,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21284 in
                                                              let uu____21324
                                                                =
                                                                let uu____21331
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21331
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21344
                                                                    =
                                                                    let uu____21347
                                                                    =
                                                                    let uu____21348
                                                                    =
                                                                    let uu____21355
                                                                    =
                                                                    let uu____21356
                                                                    =
                                                                    let uu____21367
                                                                    =
                                                                    let uu____21368
                                                                    =
                                                                    let uu____21373
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21373,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21368 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21367) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21356 in
                                                                    (uu____21355,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21348 in
                                                                    [uu____21347] in
                                                                    (d3,
                                                                    uu____21344) in
                                                              (match uu____21324
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21216
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
                            let uu____21438 =
                              let uu____21451 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21530  ->
                                   fun uu____21531  ->
                                     match (uu____21530, uu____21531) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21686 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21686 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21451 in
                            (match uu____21438 with
                             | (decls2,eqns,env01) ->
                                 let uu____21759 =
                                   let isDeclFun uu___315_21771 =
                                     match uu___315_21771 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21772 -> true
                                     | uu____21783 -> false in
                                   let uu____21784 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21784
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21759 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21824 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___316_21828  ->
                                 match uu___316_21828 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21829 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21835 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21835))) in
                      if uu____21824
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
                   let uu____21887 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21887
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
        let uu____21936 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21936 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21940 = encode_sigelt' env se in
      match uu____21940 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21956 =
                  let uu____21957 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21957 in
                [uu____21956]
            | uu____21958 ->
                let uu____21959 =
                  let uu____21962 =
                    let uu____21963 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21963 in
                  uu____21962 :: g in
                let uu____21964 =
                  let uu____21967 =
                    let uu____21968 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21968 in
                  [uu____21967] in
                FStar_List.append uu____21959 uu____21964 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21981 =
          let uu____21982 = FStar_Syntax_Subst.compress t in
          uu____21982.FStar_Syntax_Syntax.n in
        match uu____21981 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21986)) -> s = "opaque_to_smt"
        | uu____21987 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21992 =
          let uu____21993 = FStar_Syntax_Subst.compress t in
          uu____21993.FStar_Syntax_Syntax.n in
        match uu____21992 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21997)) -> s = "uninterpreted_by_smt"
        | uu____21998 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22003 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22008 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22011 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22014 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22029 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22033 =
            let uu____22034 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22034 Prims.op_Negation in
          if uu____22033
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22060 ->
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
               let uu____22080 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22080 with
               | (aname,atok,env2) ->
                   let uu____22096 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22096 with
                    | (formals,uu____22114) ->
                        let uu____22127 =
                          let uu____22132 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22132 env2 in
                        (match uu____22127 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22144 =
                                 let uu____22145 =
                                   let uu____22156 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22172  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22156,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22145 in
                               [uu____22144;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22185 =
                               let aux uu____22237 uu____22238 =
                                 match (uu____22237, uu____22238) with
                                 | ((bv,uu____22290),(env3,acc_sorts,acc)) ->
                                     let uu____22328 = gen_term_var env3 bv in
                                     (match uu____22328 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22185 with
                              | (uu____22400,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22423 =
                                      let uu____22430 =
                                        let uu____22431 =
                                          let uu____22442 =
                                            let uu____22443 =
                                              let uu____22448 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22448) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22443 in
                                          ([[app]], xs_sorts, uu____22442) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22431 in
                                      (uu____22430,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22423 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22468 =
                                      let uu____22475 =
                                        let uu____22476 =
                                          let uu____22487 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22487) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22476 in
                                      (uu____22475,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22468 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22506 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22506 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22534,uu____22535)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22536 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22536 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22553,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22559 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___317_22563  ->
                      match uu___317_22563 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22564 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22569 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22570 -> false)) in
            Prims.op_Negation uu____22559 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22579 =
               let uu____22586 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22586 env fv t quals in
             match uu____22579 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22601 =
                   let uu____22604 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22604 in
                 (uu____22601, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22612 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22612 with
           | (uu____22621,f1) ->
               let uu____22623 = encode_formula f1 env in
               (match uu____22623 with
                | (f2,decls) ->
                    let g =
                      let uu____22637 =
                        let uu____22638 =
                          let uu____22645 =
                            let uu____22648 =
                              let uu____22649 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22649 in
                            FStar_Pervasives_Native.Some uu____22648 in
                          let uu____22650 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22645, uu____22650) in
                        FStar_SMTEncoding_Util.mkAssume uu____22638 in
                      [uu____22637] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22656) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22668 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22686 =
                       let uu____22689 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22689.FStar_Syntax_Syntax.fv_name in
                     uu____22686.FStar_Syntax_Syntax.v in
                   let uu____22690 =
                     let uu____22691 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22691 in
                   if uu____22690
                   then
                     let val_decl =
                       let uu___352_22719 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___352_22719.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___352_22719.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___352_22719.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22724 = encode_sigelt' env1 val_decl in
                     match uu____22724 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22668 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22752,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22754;
                          FStar_Syntax_Syntax.lbtyp = uu____22755;
                          FStar_Syntax_Syntax.lbeff = uu____22756;
                          FStar_Syntax_Syntax.lbdef = uu____22757;_}::[]),uu____22758)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22777 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22777 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22806 =
                   let uu____22809 =
                     let uu____22810 =
                       let uu____22817 =
                         let uu____22818 =
                           let uu____22829 =
                             let uu____22830 =
                               let uu____22835 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22835) in
                             FStar_SMTEncoding_Util.mkEq uu____22830 in
                           ([[b2t_x]], [xx], uu____22829) in
                         FStar_SMTEncoding_Util.mkForall uu____22818 in
                       (uu____22817,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22810 in
                   [uu____22809] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22806 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22868,uu____22869) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___318_22878  ->
                  match uu___318_22878 with
                  | FStar_Syntax_Syntax.Discriminator uu____22879 -> true
                  | uu____22880 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22883,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22894 =
                     let uu____22895 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22895.FStar_Ident.idText in
                   uu____22894 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___319_22899  ->
                     match uu___319_22899 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22900 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22904) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___320_22921  ->
                  match uu___320_22921 with
                  | FStar_Syntax_Syntax.Projector uu____22922 -> true
                  | uu____22927 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22930 = try_lookup_free_var env l in
          (match uu____22930 with
           | FStar_Pervasives_Native.Some uu____22937 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___353_22941 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___353_22941.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___353_22941.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___353_22941.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22948) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22966) ->
          let uu____22975 = encode_sigelts env ses in
          (match uu____22975 with
           | (g,env1) ->
               let uu____22992 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___321_23015  ->
                         match uu___321_23015 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23016;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23017;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23018;_}
                             -> false
                         | uu____23021 -> true)) in
               (match uu____22992 with
                | (g',inversions) ->
                    let uu____23036 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___322_23057  ->
                              match uu___322_23057 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23058 ->
                                  true
                              | uu____23069 -> false)) in
                    (match uu____23036 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23087,tps,k,uu____23090,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___323_23107  ->
                    match uu___323_23107 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23108 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23117 = c in
              match uu____23117 with
              | (name,args,uu____23122,uu____23123,uu____23124) ->
                  let uu____23129 =
                    let uu____23130 =
                      let uu____23141 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23158  ->
                                match uu____23158 with
                                | (uu____23165,sort,uu____23167) -> sort)) in
                      (name, uu____23141, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23130 in
                  [uu____23129]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23194 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23200 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23200 FStar_Option.isNone)) in
            if uu____23194
            then []
            else
              (let uu____23232 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23232 with
               | (xxsym,xx) ->
                   let uu____23241 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23280  ->
                             fun l  ->
                               match uu____23280 with
                               | (out,decls) ->
                                   let uu____23300 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23300 with
                                    | (uu____23311,data_t) ->
                                        let uu____23313 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23313 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23359 =
                                                 let uu____23360 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23360.FStar_Syntax_Syntax.n in
                                               match uu____23359 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23371,indices) ->
                                                   indices
                                               | uu____23393 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23417  ->
                                                         match uu____23417
                                                         with
                                                         | (x,uu____23423) ->
                                                             let uu____23424
                                                               =
                                                               let uu____23425
                                                                 =
                                                                 let uu____23432
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23432,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23425 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23424)
                                                    env) in
                                             let uu____23435 =
                                               encode_args indices env1 in
                                             (match uu____23435 with
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
                                                      let uu____23461 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23477
                                                                 =
                                                                 let uu____23482
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23482,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23477)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23461
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23485 =
                                                      let uu____23486 =
                                                        let uu____23491 =
                                                          let uu____23492 =
                                                            let uu____23497 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23497,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23492 in
                                                        (out, uu____23491) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23486 in
                                                    (uu____23485,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23241 with
                    | (data_ax,decls) ->
                        let uu____23510 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23510 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23521 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23521 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23525 =
                                 let uu____23532 =
                                   let uu____23533 =
                                     let uu____23544 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23559 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23544,
                                       uu____23559) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23533 in
                                 let uu____23574 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23532,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23574) in
                               FStar_SMTEncoding_Util.mkAssume uu____23525 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23577 =
            let uu____23590 =
              let uu____23591 = FStar_Syntax_Subst.compress k in
              uu____23591.FStar_Syntax_Syntax.n in
            match uu____23590 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23636 -> (tps, k) in
          (match uu____23577 with
           | (formals,res) ->
               let uu____23659 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23659 with
                | (formals1,res1) ->
                    let uu____23670 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23670 with
                     | (vars,guards,env',binder_decls,uu____23695) ->
                         let uu____23708 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23708 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23727 =
                                  let uu____23734 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23734) in
                                FStar_SMTEncoding_Util.mkApp uu____23727 in
                              let uu____23743 =
                                let tname_decl =
                                  let uu____23753 =
                                    let uu____23754 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23786  ->
                                              match uu____23786 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23799 = varops.next_id () in
                                    (tname, uu____23754,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23799, false) in
                                  constructor_or_logic_type_decl uu____23753 in
                                let uu____23808 =
                                  match vars with
                                  | [] ->
                                      let uu____23821 =
                                        let uu____23822 =
                                          let uu____23825 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23825 in
                                        push_free_var env1 t tname
                                          uu____23822 in
                                      ([], uu____23821)
                                  | uu____23832 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23841 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23841 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23855 =
                                          let uu____23862 =
                                            let uu____23863 =
                                              let uu____23878 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23878) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23863 in
                                          (uu____23862,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23855 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23808 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23743 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23918 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23918 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23936 =
                                               let uu____23937 =
                                                 let uu____23944 =
                                                   let uu____23945 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23945 in
                                                 (uu____23944,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23937 in
                                             [uu____23936]
                                           else [] in
                                         let uu____23949 =
                                           let uu____23952 =
                                             let uu____23955 =
                                               let uu____23956 =
                                                 let uu____23963 =
                                                   let uu____23964 =
                                                     let uu____23975 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23975) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23964 in
                                                 (uu____23963,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23956 in
                                             [uu____23955] in
                                           FStar_List.append karr uu____23952 in
                                         FStar_List.append decls1 uu____23949 in
                                   let aux =
                                     let uu____23991 =
                                       let uu____23994 =
                                         inversion_axioms tapp vars in
                                       let uu____23997 =
                                         let uu____24000 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24000] in
                                       FStar_List.append uu____23994
                                         uu____23997 in
                                     FStar_List.append kindingAx uu____23991 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24007,uu____24008,uu____24009,uu____24010,uu____24011)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24019,t,uu____24021,n_tps,uu____24023) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24031 = new_term_constant_and_tok_from_lid env d in
          (match uu____24031 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24048 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24048 with
                | (formals,t_res) ->
                    let uu____24083 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24083 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24097 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24097 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24167 =
                                            mk_term_projector_name d x in
                                          (uu____24167,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24169 =
                                  let uu____24188 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24188, true) in
                                FStar_All.pipe_right uu____24169
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
                              let uu____24227 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24227 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24239::uu____24240 ->
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
                                         let uu____24285 =
                                           let uu____24296 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24296) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24285
                                     | uu____24321 -> tok_typing in
                                   let uu____24330 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24330 with
                                    | (vars',guards',env'',decls_formals,uu____24355)
                                        ->
                                        let uu____24368 =
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
                                        (match uu____24368 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24399 ->
                                                   let uu____24406 =
                                                     let uu____24407 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24407 in
                                                   [uu____24406] in
                                             let encode_elim uu____24417 =
                                               let uu____24418 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24418 with
                                               | (head1,args) ->
                                                   let uu____24461 =
                                                     let uu____24462 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24462.FStar_Syntax_Syntax.n in
                                                   (match uu____24461 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24472;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24473;_},uu____24474)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24480 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24480
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
                                                                 | uu____24523
                                                                    ->
                                                                    let uu____24524
                                                                    =
                                                                    let uu____24525
                                                                    =
                                                                    let uu____24530
                                                                    =
                                                                    let uu____24531
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24531 in
                                                                    (uu____24530,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24525 in
                                                                    FStar_Exn.raise
                                                                    uu____24524 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24547
                                                                    =
                                                                    let uu____24548
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24548 in
                                                                    if
                                                                    uu____24547
                                                                    then
                                                                    let uu____24561
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24561]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24563
                                                               =
                                                               let uu____24576
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24626
                                                                     ->
                                                                    fun
                                                                    uu____24627
                                                                     ->
                                                                    match 
                                                                    (uu____24626,
                                                                    uu____24627)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24722
                                                                    =
                                                                    let uu____24729
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24729 in
                                                                    (match uu____24722
                                                                    with
                                                                    | 
                                                                    (uu____24742,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24750
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24750
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24752
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24752
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
                                                                 uu____24576 in
                                                             (match uu____24563
                                                              with
                                                              | (uu____24767,arg_vars,elim_eqns_or_guards,uu____24770)
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
                                                                    let uu____24800
                                                                    =
                                                                    let uu____24807
                                                                    =
                                                                    let uu____24808
                                                                    =
                                                                    let uu____24819
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24830
                                                                    =
                                                                    let uu____24831
                                                                    =
                                                                    let uu____24836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24836) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24831 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24819,
                                                                    uu____24830) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24808 in
                                                                    (uu____24807,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24800 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24859
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24859,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24861
                                                                    =
                                                                    let uu____24868
                                                                    =
                                                                    let uu____24869
                                                                    =
                                                                    let uu____24880
                                                                    =
                                                                    let uu____24885
                                                                    =
                                                                    let uu____24888
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24888] in
                                                                    [uu____24885] in
                                                                    let uu____24893
                                                                    =
                                                                    let uu____24894
                                                                    =
                                                                    let uu____24899
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24900
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24899,
                                                                    uu____24900) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24894 in
                                                                    (uu____24880,
                                                                    [x],
                                                                    uu____24893) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24869 in
                                                                    let uu____24919
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24868,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24919) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24861
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24926
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
                                                                    (let uu____24954
                                                                    =
                                                                    let uu____24955
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24955
                                                                    dapp1 in
                                                                    [uu____24954]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24926
                                                                    FStar_List.flatten in
                                                                    let uu____24962
                                                                    =
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24970
                                                                    =
                                                                    let uu____24981
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24992
                                                                    =
                                                                    let uu____24993
                                                                    =
                                                                    let uu____24998
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24998) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24993 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24981,
                                                                    uu____24992) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24970 in
                                                                    (uu____24969,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24962) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25019 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25019
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
                                                                 | uu____25062
                                                                    ->
                                                                    let uu____25063
                                                                    =
                                                                    let uu____25064
                                                                    =
                                                                    let uu____25069
                                                                    =
                                                                    let uu____25070
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25070 in
                                                                    (uu____25069,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25064 in
                                                                    FStar_Exn.raise
                                                                    uu____25063 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25086
                                                                    =
                                                                    let uu____25087
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25087 in
                                                                    if
                                                                    uu____25086
                                                                    then
                                                                    let uu____25100
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25100]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25102
                                                               =
                                                               let uu____25115
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25165
                                                                     ->
                                                                    fun
                                                                    uu____25166
                                                                     ->
                                                                    match 
                                                                    (uu____25165,
                                                                    uu____25166)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25261
                                                                    =
                                                                    let uu____25268
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25268 in
                                                                    (match uu____25261
                                                                    with
                                                                    | 
                                                                    (uu____25281,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25289
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25289
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25291
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25291
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
                                                                 uu____25115 in
                                                             (match uu____25102
                                                              with
                                                              | (uu____25306,arg_vars,elim_eqns_or_guards,uu____25309)
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
                                                                    let uu____25339
                                                                    =
                                                                    let uu____25346
                                                                    =
                                                                    let uu____25347
                                                                    =
                                                                    let uu____25358
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25369
                                                                    =
                                                                    let uu____25370
                                                                    =
                                                                    let uu____25375
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25375) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25370 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25358,
                                                                    uu____25369) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25347 in
                                                                    (uu____25346,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25339 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25398
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25398,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25400
                                                                    =
                                                                    let uu____25407
                                                                    =
                                                                    let uu____25408
                                                                    =
                                                                    let uu____25419
                                                                    =
                                                                    let uu____25424
                                                                    =
                                                                    let uu____25427
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25427] in
                                                                    [uu____25424] in
                                                                    let uu____25432
                                                                    =
                                                                    let uu____25433
                                                                    =
                                                                    let uu____25438
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25438,
                                                                    uu____25439) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25433 in
                                                                    (uu____25419,
                                                                    [x],
                                                                    uu____25432) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25408 in
                                                                    let uu____25458
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25407,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25458) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25400
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25465
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
                                                                    (let uu____25493
                                                                    =
                                                                    let uu____25494
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25494
                                                                    dapp1 in
                                                                    [uu____25493]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25465
                                                                    FStar_List.flatten in
                                                                    let uu____25501
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25509
                                                                    =
                                                                    let uu____25520
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25531
                                                                    =
                                                                    let uu____25532
                                                                    =
                                                                    let uu____25537
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25537) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25532 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25520,
                                                                    uu____25531) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25509 in
                                                                    (uu____25508,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25501) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25556 ->
                                                        ((let uu____25558 =
                                                            let uu____25559 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25560 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25559
                                                              uu____25560 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25558);
                                                         ([], []))) in
                                             let uu____25565 = encode_elim () in
                                             (match uu____25565 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25585 =
                                                      let uu____25588 =
                                                        let uu____25591 =
                                                          let uu____25594 =
                                                            let uu____25597 =
                                                              let uu____25598
                                                                =
                                                                let uu____25609
                                                                  =
                                                                  let uu____25612
                                                                    =
                                                                    let uu____25613
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25613 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25612 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25609) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25598 in
                                                            [uu____25597] in
                                                          let uu____25618 =
                                                            let uu____25621 =
                                                              let uu____25624
                                                                =
                                                                let uu____25627
                                                                  =
                                                                  let uu____25630
                                                                    =
                                                                    let uu____25633
                                                                    =
                                                                    let uu____25636
                                                                    =
                                                                    let uu____25637
                                                                    =
                                                                    let uu____25644
                                                                    =
                                                                    let uu____25645
                                                                    =
                                                                    let uu____25656
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25656) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25645 in
                                                                    (uu____25644,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25637 in
                                                                    let uu____25669
                                                                    =
                                                                    let uu____25672
                                                                    =
                                                                    let uu____25673
                                                                    =
                                                                    let uu____25680
                                                                    =
                                                                    let uu____25681
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25692,
                                                                    uu____25703) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25681 in
                                                                    (uu____25680,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25673 in
                                                                    [uu____25672] in
                                                                    uu____25636
                                                                    ::
                                                                    uu____25669 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25633 in
                                                                  FStar_List.append
                                                                    uu____25630
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25627 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25624 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25621 in
                                                          FStar_List.append
                                                            uu____25594
                                                            uu____25618 in
                                                        FStar_List.append
                                                          decls3 uu____25591 in
                                                      FStar_List.append
                                                        decls2 uu____25588 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25585 in
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
           (fun uu____25749  ->
              fun se  ->
                match uu____25749 with
                | (g,env1) ->
                    let uu____25769 = encode_sigelt env1 se in
                    (match uu____25769 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25826 =
        match uu____25826 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25858 ->
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
                 ((let uu____25864 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25864
                   then
                     let uu____25865 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25866 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25867 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25865 uu____25866 uu____25867
                   else ());
                  (let uu____25869 = encode_term t1 env1 in
                   match uu____25869 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25885 =
                         let uu____25892 =
                           let uu____25893 =
                             let uu____25894 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25894
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25893 in
                         new_term_constant_from_string env1 x uu____25892 in
                       (match uu____25885 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25910 = FStar_Options.log_queries () in
                              if uu____25910
                              then
                                let uu____25913 =
                                  let uu____25914 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25915 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25916 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25914 uu____25915 uu____25916 in
                                FStar_Pervasives_Native.Some uu____25913
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25932,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25946 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25946 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25969,se,uu____25971) ->
                 let uu____25976 = encode_sigelt env1 se in
                 (match uu____25976 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25993,se) ->
                 let uu____25999 = encode_sigelt env1 se in
                 (match uu____25999 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26016 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26016 with | (uu____26039,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26051 'Auu____26052 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26052,'Auu____26051)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26120  ->
              match uu____26120 with
              | (l,uu____26132,uu____26133) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26179  ->
              match uu____26179 with
              | (l,uu____26193,uu____26194) ->
                  let uu____26203 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26204 =
                    let uu____26207 =
                      let uu____26208 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26208 in
                    [uu____26207] in
                  uu____26203 :: uu____26204)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26229 =
      let uu____26232 =
        let uu____26233 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26236 =
          let uu____26237 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26237 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26233;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26236
        } in
      [uu____26232] in
    FStar_ST.op_Colon_Equals last_env uu____26229
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26294 = FStar_ST.op_Bang last_env in
      match uu____26294 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26348 ->
          let uu___354_26351 = e in
          let uu____26352 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___354_26351.bindings);
            depth = (uu___354_26351.depth);
            tcenv;
            warn = (uu___354_26351.warn);
            cache = (uu___354_26351.cache);
            nolabels = (uu___354_26351.nolabels);
            use_zfuel_name = (uu___354_26351.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___354_26351.encode_non_total_function_typ);
            current_module_name = uu____26352
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26356 = FStar_ST.op_Bang last_env in
    match uu____26356 with
    | [] -> failwith "Empty env stack"
    | uu____26409::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26465  ->
    let uu____26466 = FStar_ST.op_Bang last_env in
    match uu____26466 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___355_26527 = hd1 in
          {
            bindings = (uu___355_26527.bindings);
            depth = (uu___355_26527.depth);
            tcenv = (uu___355_26527.tcenv);
            warn = (uu___355_26527.warn);
            cache = refs;
            nolabels = (uu___355_26527.nolabels);
            use_zfuel_name = (uu___355_26527.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___355_26527.encode_non_total_function_typ);
            current_module_name = (uu___355_26527.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26580  ->
    let uu____26581 = FStar_ST.op_Bang last_env in
    match uu____26581 with
    | [] -> failwith "Popping an empty stack"
    | uu____26634::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26725::uu____26726,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___356_26734 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___356_26734.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___356_26734.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___356_26734.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26735 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26750 =
        let uu____26753 =
          let uu____26754 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26754 in
        let uu____26755 = open_fact_db_tags env in uu____26753 :: uu____26755 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26750
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
      let uu____26777 = encode_sigelt env se in
      match uu____26777 with
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
        let uu____26813 = FStar_Options.log_queries () in
        if uu____26813
        then
          let uu____26816 =
            let uu____26817 =
              let uu____26818 =
                let uu____26819 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26819 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26818 in
            FStar_SMTEncoding_Term.Caption uu____26817 in
          uu____26816 :: decls
        else decls in
      (let uu____26830 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26830
       then
         let uu____26831 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26831
       else ());
      (let env =
         let uu____26834 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26834 tcenv in
       let uu____26835 = encode_top_level_facts env se in
       match uu____26835 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26849 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26849)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26861 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26861
       then
         let uu____26862 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26862
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26897  ->
                 fun se  ->
                   match uu____26897 with
                   | (g,env2) ->
                       let uu____26917 = encode_top_level_facts env2 se in
                       (match uu____26917 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26940 =
         encode_signature
           (let uu___357_26949 = env in
            {
              bindings = (uu___357_26949.bindings);
              depth = (uu___357_26949.depth);
              tcenv = (uu___357_26949.tcenv);
              warn = false;
              cache = (uu___357_26949.cache);
              nolabels = (uu___357_26949.nolabels);
              use_zfuel_name = (uu___357_26949.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___357_26949.encode_non_total_function_typ);
              current_module_name = (uu___357_26949.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26940 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26966 = FStar_Options.log_queries () in
             if uu____26966
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___358_26974 = env1 in
               {
                 bindings = (uu___358_26974.bindings);
                 depth = (uu___358_26974.depth);
                 tcenv = (uu___358_26974.tcenv);
                 warn = true;
                 cache = (uu___358_26974.cache);
                 nolabels = (uu___358_26974.nolabels);
                 use_zfuel_name = (uu___358_26974.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___358_26974.encode_non_total_function_typ);
                 current_module_name = (uu___358_26974.current_module_name)
               });
            (let uu____26976 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26976
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
        (let uu____27028 =
           let uu____27029 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27029.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27028);
        (let env =
           let uu____27031 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27031 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27043 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27078 = aux rest in
                 (match uu____27078 with
                  | (out,rest1) ->
                      let t =
                        let uu____27108 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27108 with
                        | FStar_Pervasives_Native.Some uu____27113 ->
                            let uu____27114 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27114
                              x.FStar_Syntax_Syntax.sort
                        | uu____27115 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27119 =
                        let uu____27122 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___359_27125 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___359_27125.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___359_27125.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27122 :: out in
                      (uu____27119, rest1))
             | uu____27130 -> ([], bindings1) in
           let uu____27137 = aux bindings in
           match uu____27137 with
           | (closing,bindings1) ->
               let uu____27162 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27162, bindings1) in
         match uu____27043 with
         | (q1,bindings1) ->
             let uu____27185 =
               let uu____27190 =
                 FStar_List.filter
                   (fun uu___324_27195  ->
                      match uu___324_27195 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27196 ->
                          false
                      | uu____27203 -> true) bindings1 in
               encode_env_bindings env uu____27190 in
             (match uu____27185 with
              | (env_decls,env1) ->
                  ((let uu____27221 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27221
                    then
                      let uu____27222 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27222
                    else ());
                   (let uu____27224 = encode_formula q1 env1 in
                    match uu____27224 with
                    | (phi,qdecls) ->
                        let uu____27245 =
                          let uu____27250 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27250 phi in
                        (match uu____27245 with
                         | (labels,phi1) ->
                             let uu____27267 = encode_labels labels in
                             (match uu____27267 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27304 =
                                      let uu____27311 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27312 =
                                        varops.mk_unique "@query" in
                                      (uu____27311,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27312) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27304 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))