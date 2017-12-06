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
                         let uu____8247 =
                           let uu____8248 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8248 in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8247) in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8242);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8250 =
                       (is_impure rc) &&
                         (let uu____8252 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8252) in
                     if uu____8250
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8259 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8259 with
                        | (vars,guards,envbody,decls,uu____8284) ->
                            let body2 =
                              let uu____8298 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8298
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8300 = encode_term body2 envbody in
                            (match uu____8300 with
                             | (body3,decls') ->
                                 let uu____8311 =
                                   let uu____8320 = codomain_eff rc in
                                   match uu____8320 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8339 = encode_term tfun env in
                                       (match uu____8339 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8311 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8371 =
                                          let uu____8382 =
                                            let uu____8383 =
                                              let uu____8388 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8388, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8383 in
                                          ([], vars, uu____8382) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8371 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8400 =
                                              let uu____8403 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8403
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8400 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8422 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8422 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8430 =
                                             let uu____8431 =
                                               let uu____8438 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8438) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8431 in
                                           (uu____8430,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8449 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8449 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8460 =
                                                    let uu____8461 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8461 = cache_size in
                                                  if uu____8460
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
                                                    let uu____8477 =
                                                      let uu____8478 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8478 in
                                                    varops.mk_unique
                                                      uu____8477 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8485 =
                                                    let uu____8492 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8492) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8485 in
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
                                                      let uu____8510 =
                                                        let uu____8511 =
                                                          let uu____8518 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8518,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8511 in
                                                      [uu____8510] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8531 =
                                                    let uu____8538 =
                                                      let uu____8539 =
                                                        let uu____8550 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8550) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8539 in
                                                    (uu____8538,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8531 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8567 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8567);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8570,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8571;
                          FStar_Syntax_Syntax.lbunivs = uu____8572;
                          FStar_Syntax_Syntax.lbtyp = uu____8573;
                          FStar_Syntax_Syntax.lbeff = uu____8574;
                          FStar_Syntax_Syntax.lbdef = uu____8575;_}::uu____8576),uu____8577)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8603;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8605;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8626 ->
           (FStar_Errors.diag t.FStar_Syntax_Syntax.pos
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
              let uu____8696 = encode_term e1 env in
              match uu____8696 with
              | (ee1,decls1) ->
                  let uu____8707 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8707 with
                   | (xs,e21) ->
                       let uu____8732 = FStar_List.hd xs in
                       (match uu____8732 with
                        | (x1,uu____8746) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8748 = encode_body e21 env' in
                            (match uu____8748 with
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
            let uu____8780 =
              let uu____8787 =
                let uu____8788 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8788 in
              gen_term_var env uu____8787 in
            match uu____8780 with
            | (scrsym,scr',env1) ->
                let uu____8796 = encode_term e env1 in
                (match uu____8796 with
                 | (scr,decls) ->
                     let uu____8807 =
                       let encode_branch b uu____8832 =
                         match uu____8832 with
                         | (else_case,decls1) ->
                             let uu____8851 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8851 with
                              | (p,w,br) ->
                                  let uu____8877 = encode_pat env1 p in
                                  (match uu____8877 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8914  ->
                                                   match uu____8914 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8921 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8943 =
                                               encode_term w1 env2 in
                                             (match uu____8943 with
                                              | (w2,decls2) ->
                                                  let uu____8956 =
                                                    let uu____8957 =
                                                      let uu____8962 =
                                                        let uu____8963 =
                                                          let uu____8968 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8968) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8963 in
                                                      (guard, uu____8962) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8957 in
                                                  (uu____8956, decls2)) in
                                       (match uu____8921 with
                                        | (guard1,decls2) ->
                                            let uu____8981 =
                                              encode_br br env2 in
                                            (match uu____8981 with
                                             | (br1,decls3) ->
                                                 let uu____8994 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8994,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8807 with
                      | (match_tm,decls1) ->
                          let uu____9013 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9013, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9053 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9053
       then
         let uu____9054 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9054
       else ());
      (let uu____9056 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9056 with
       | (vars,pat_term) ->
           let uu____9073 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9126  ->
                     fun v1  ->
                       match uu____9126 with
                       | (env1,vars1) ->
                           let uu____9178 = gen_term_var env1 v1 in
                           (match uu____9178 with
                            | (xx,uu____9200,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9073 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9279 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9280 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9281 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9289 = encode_const c env1 in
                      (match uu____9289 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9303::uu____9304 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9307 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9330 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9330 with
                        | (uu____9337,uu____9338::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9341 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9374  ->
                                  match uu____9374 with
                                  | (arg,uu____9382) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9388 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9388)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9415) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9446 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9469 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9513  ->
                                  match uu____9513 with
                                  | (arg,uu____9527) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9533 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9533)) in
                      FStar_All.pipe_right uu____9469 FStar_List.flatten in
                let pat_term1 uu____9561 = encode_term pat_term env1 in
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
      let uu____9571 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9609  ->
                fun uu____9610  ->
                  match (uu____9609, uu____9610) with
                  | ((tms,decls),(t,uu____9646)) ->
                      let uu____9667 = encode_term t env in
                      (match uu____9667 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9571 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9724 = FStar_Syntax_Util.list_elements e in
        match uu____9724 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9745 =
          let uu____9760 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9760 FStar_Syntax_Util.head_and_args in
        match uu____9745 with
        | (head1,args) ->
            let uu____9799 =
              let uu____9812 =
                let uu____9813 = FStar_Syntax_Util.un_uinst head1 in
                uu____9813.FStar_Syntax_Syntax.n in
              (uu____9812, args) in
            (match uu____9799 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9827,uu____9828)::(e,uu____9830)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9865 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9901 =
            let uu____9916 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9916 FStar_Syntax_Util.head_and_args in
          match uu____9901 with
          | (head1,args) ->
              let uu____9957 =
                let uu____9970 =
                  let uu____9971 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9971.FStar_Syntax_Syntax.n in
                (uu____9970, args) in
              (match uu____9957 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9988)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10015 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10037 = smt_pat_or1 t1 in
            (match uu____10037 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10053 = list_elements1 e in
                 FStar_All.pipe_right uu____10053
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10071 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10071
                           (FStar_List.map one_pat)))
             | uu____10082 ->
                 let uu____10087 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10087])
        | uu____10108 ->
            let uu____10111 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10111] in
      let uu____10132 =
        let uu____10151 =
          let uu____10152 = FStar_Syntax_Subst.compress t in
          uu____10152.FStar_Syntax_Syntax.n in
        match uu____10151 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10191 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10191 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10234;
                        FStar_Syntax_Syntax.effect_name = uu____10235;
                        FStar_Syntax_Syntax.result_typ = uu____10236;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10238)::(post,uu____10240)::(pats,uu____10242)::[];
                        FStar_Syntax_Syntax.flags = uu____10243;_}
                      ->
                      let uu____10284 = lemma_pats pats in
                      (binders1, pre, post, uu____10284)
                  | uu____10301 -> failwith "impos"))
        | uu____10320 -> failwith "Impos" in
      match uu____10132 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___335_10368 = env in
            {
              bindings = (uu___335_10368.bindings);
              depth = (uu___335_10368.depth);
              tcenv = (uu___335_10368.tcenv);
              warn = (uu___335_10368.warn);
              cache = (uu___335_10368.cache);
              nolabels = (uu___335_10368.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___335_10368.encode_non_total_function_typ);
              current_module_name = (uu___335_10368.current_module_name)
            } in
          let uu____10369 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10369 with
           | (vars,guards,env2,decls,uu____10394) ->
               let uu____10407 =
                 let uu____10420 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10464 =
                             let uu____10473 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10473
                               FStar_List.unzip in
                           match uu____10464 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10420 FStar_List.unzip in
               (match uu____10407 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___336_10585 = env2 in
                      {
                        bindings = (uu___336_10585.bindings);
                        depth = (uu___336_10585.depth);
                        tcenv = (uu___336_10585.tcenv);
                        warn = (uu___336_10585.warn);
                        cache = (uu___336_10585.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___336_10585.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___336_10585.encode_non_total_function_typ);
                        current_module_name =
                          (uu___336_10585.current_module_name)
                      } in
                    let uu____10586 =
                      let uu____10591 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10591 env3 in
                    (match uu____10586 with
                     | (pre1,decls'') ->
                         let uu____10598 =
                           let uu____10603 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10603 env3 in
                         (match uu____10598 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10613 =
                                let uu____10614 =
                                  let uu____10625 =
                                    let uu____10626 =
                                      let uu____10631 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10631, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10626 in
                                  (pats, vars, uu____10625) in
                                FStar_SMTEncoding_Util.mkForall uu____10614 in
                              (uu____10613, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10650 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10650
        then
          let uu____10651 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10652 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10651 uu____10652
        else () in
      let enc f r l =
        let uu____10685 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10713 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10713 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10685 with
        | (decls,args) ->
            let uu____10742 =
              let uu___337_10743 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___337_10743.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___337_10743.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10742, decls) in
      let const_op f r uu____10774 =
        let uu____10787 = f r in (uu____10787, []) in
      let un_op f l =
        let uu____10806 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10806 in
      let bin_op f uu___311_10822 =
        match uu___311_10822 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10833 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10867 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10890  ->
                 match uu____10890 with
                 | (t,uu____10904) ->
                     let uu____10905 = encode_formula t env in
                     (match uu____10905 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10867 with
        | (decls,phis) ->
            let uu____10934 =
              let uu___338_10935 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___338_10935.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___338_10935.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10934, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10996  ->
               match uu____10996 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11015) -> false
                    | uu____11016 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11031 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11031
        else
          (let uu____11045 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11045 r rf) in
      let mk_imp1 r uu___312_11070 =
        match uu___312_11070 with
        | (lhs,uu____11076)::(rhs,uu____11078)::[] ->
            let uu____11105 = encode_formula rhs env in
            (match uu____11105 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11120) ->
                      (l1, decls1)
                  | uu____11125 ->
                      let uu____11126 = encode_formula lhs env in
                      (match uu____11126 with
                       | (l2,decls2) ->
                           let uu____11137 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11137, (FStar_List.append decls1 decls2)))))
        | uu____11140 -> failwith "impossible" in
      let mk_ite r uu___313_11161 =
        match uu___313_11161 with
        | (guard,uu____11167)::(_then,uu____11169)::(_else,uu____11171)::[]
            ->
            let uu____11208 = encode_formula guard env in
            (match uu____11208 with
             | (g,decls1) ->
                 let uu____11219 = encode_formula _then env in
                 (match uu____11219 with
                  | (t,decls2) ->
                      let uu____11230 = encode_formula _else env in
                      (match uu____11230 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11244 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11269 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11269 in
      let connectives =
        let uu____11287 =
          let uu____11300 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11300) in
        let uu____11317 =
          let uu____11332 =
            let uu____11345 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11345) in
          let uu____11362 =
            let uu____11377 =
              let uu____11392 =
                let uu____11405 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11405) in
              let uu____11422 =
                let uu____11437 =
                  let uu____11452 =
                    let uu____11465 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11465) in
                  [uu____11452;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11437 in
              uu____11392 :: uu____11422 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11377 in
          uu____11332 :: uu____11362 in
        uu____11287 :: uu____11317 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11786 = encode_formula phi' env in
            (match uu____11786 with
             | (phi2,decls) ->
                 let uu____11797 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11797, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11798 ->
            let uu____11805 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11805 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11844 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11844 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11856;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11858;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11879 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11879 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11926::(x,uu____11928)::(t,uu____11930)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11977 = encode_term x env in
                 (match uu____11977 with
                  | (x1,decls) ->
                      let uu____11988 = encode_term t env in
                      (match uu____11988 with
                       | (t1,decls') ->
                           let uu____11999 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11999, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12004)::(msg,uu____12006)::(phi2,uu____12008)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12053 =
                   let uu____12058 =
                     let uu____12059 = FStar_Syntax_Subst.compress r in
                     uu____12059.FStar_Syntax_Syntax.n in
                   let uu____12062 =
                     let uu____12063 = FStar_Syntax_Subst.compress msg in
                     uu____12063.FStar_Syntax_Syntax.n in
                   (uu____12058, uu____12062) in
                 (match uu____12053 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12072))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12078 -> fallback phi2)
             | uu____12083 when head_redex env head2 ->
                 let uu____12096 = whnf env phi1 in
                 encode_formula uu____12096 env
             | uu____12097 ->
                 let uu____12110 = encode_term phi1 env in
                 (match uu____12110 with
                  | (tt,decls) ->
                      let uu____12121 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___339_12124 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___339_12124.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___339_12124.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12121, decls)))
        | uu____12125 ->
            let uu____12126 = encode_term phi1 env in
            (match uu____12126 with
             | (tt,decls) ->
                 let uu____12137 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___340_12140 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___340_12140.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___340_12140.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12137, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12176 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12176 with
        | (vars,guards,env2,decls,uu____12215) ->
            let uu____12228 =
              let uu____12241 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12289 =
                          let uu____12298 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12328  ->
                                    match uu____12328 with
                                    | (t,uu____12338) ->
                                        encode_term t
                                          (let uu___341_12340 = env2 in
                                           {
                                             bindings =
                                               (uu___341_12340.bindings);
                                             depth = (uu___341_12340.depth);
                                             tcenv = (uu___341_12340.tcenv);
                                             warn = (uu___341_12340.warn);
                                             cache = (uu___341_12340.cache);
                                             nolabels =
                                               (uu___341_12340.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___341_12340.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___341_12340.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12298 FStar_List.unzip in
                        match uu____12289 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12241 FStar_List.unzip in
            (match uu____12228 with
             | (pats,decls') ->
                 let uu____12439 = encode_formula body env2 in
                 (match uu____12439 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12471;
                             FStar_SMTEncoding_Term.rng = uu____12472;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12487 -> guards in
                      let uu____12492 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12492, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12552  ->
                   match uu____12552 with
                   | (x,uu____12558) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12566 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12578 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12578) uu____12566 tl1 in
             let uu____12581 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12608  ->
                       match uu____12608 with
                       | (b,uu____12614) ->
                           let uu____12615 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12615)) in
             (match uu____12581 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12621) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12635 =
                    let uu____12640 =
                      let uu____12641 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12641 in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12640) in
                  FStar_Errors.log_issue pos uu____12635) in
       let uu____12642 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12642 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12651 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12709  ->
                     match uu____12709 with
                     | (l,uu____12723) -> FStar_Ident.lid_equals op l)) in
           (match uu____12651 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12756,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12796 = encode_q_body env vars pats body in
             match uu____12796 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12841 =
                     let uu____12852 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12852) in
                   FStar_SMTEncoding_Term.mkForall uu____12841
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12871 = encode_q_body env vars pats body in
             match uu____12871 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12915 =
                   let uu____12916 =
                     let uu____12927 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12927) in
                   FStar_SMTEncoding_Term.mkExists uu____12916
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12915, decls))))
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
  let uu____13020 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13020 with
  | (asym,a) ->
      let uu____13027 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13027 with
       | (xsym,x) ->
           let uu____13034 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13034 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13078 =
                      let uu____13089 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13089, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13078 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13115 =
                      let uu____13122 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13122) in
                    FStar_SMTEncoding_Util.mkApp uu____13115 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13135 =
                    let uu____13138 =
                      let uu____13141 =
                        let uu____13144 =
                          let uu____13145 =
                            let uu____13152 =
                              let uu____13153 =
                                let uu____13164 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13164) in
                              FStar_SMTEncoding_Util.mkForall uu____13153 in
                            (uu____13152, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13145 in
                        let uu____13181 =
                          let uu____13184 =
                            let uu____13185 =
                              let uu____13192 =
                                let uu____13193 =
                                  let uu____13204 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13204) in
                                FStar_SMTEncoding_Util.mkForall uu____13193 in
                              (uu____13192,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13185 in
                          [uu____13184] in
                        uu____13144 :: uu____13181 in
                      xtok_decl :: uu____13141 in
                    xname_decl :: uu____13138 in
                  (xtok1, uu____13135) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13295 =
                    let uu____13308 =
                      let uu____13317 =
                        let uu____13318 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13318 in
                      quant axy uu____13317 in
                    (FStar_Parser_Const.op_Eq, uu____13308) in
                  let uu____13327 =
                    let uu____13342 =
                      let uu____13355 =
                        let uu____13364 =
                          let uu____13365 =
                            let uu____13366 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13366 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13365 in
                        quant axy uu____13364 in
                      (FStar_Parser_Const.op_notEq, uu____13355) in
                    let uu____13375 =
                      let uu____13390 =
                        let uu____13403 =
                          let uu____13412 =
                            let uu____13413 =
                              let uu____13414 =
                                let uu____13419 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13420 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13419, uu____13420) in
                              FStar_SMTEncoding_Util.mkLT uu____13414 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13413 in
                          quant xy uu____13412 in
                        (FStar_Parser_Const.op_LT, uu____13403) in
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
                                FStar_SMTEncoding_Util.mkLTE uu____13468 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13467 in
                            quant xy uu____13466 in
                          (FStar_Parser_Const.op_LTE, uu____13457) in
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
                                  FStar_SMTEncoding_Util.mkGT uu____13522 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13521 in
                              quant xy uu____13520 in
                            (FStar_Parser_Const.op_GT, uu____13511) in
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
                                    FStar_SMTEncoding_Util.mkGTE uu____13576 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13575 in
                                quant xy uu____13574 in
                              (FStar_Parser_Const.op_GTE, uu____13565) in
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
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13630 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13629 in
                                  quant xy uu____13628 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13619) in
                              let uu____13645 =
                                let uu____13660 =
                                  let uu____13673 =
                                    let uu____13682 =
                                      let uu____13683 =
                                        let uu____13684 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13684 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13683 in
                                    quant qx uu____13682 in
                                  (FStar_Parser_Const.op_Minus, uu____13673) in
                                let uu____13693 =
                                  let uu____13708 =
                                    let uu____13721 =
                                      let uu____13730 =
                                        let uu____13731 =
                                          let uu____13732 =
                                            let uu____13737 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13738 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13737, uu____13738) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13732 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13731 in
                                      quant xy uu____13730 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13721) in
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
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13786 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13785 in
                                        quant xy uu____13784 in
                                      (FStar_Parser_Const.op_Multiply,
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
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13840 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13839 in
                                          quant xy uu____13838 in
                                        (FStar_Parser_Const.op_Division,
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
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13894 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13893 in
                                            quant xy uu____13892 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13883) in
                                        let uu____13909 =
                                          let uu____13924 =
                                            let uu____13937 =
                                              let uu____13946 =
                                                let uu____13947 =
                                                  let uu____13948 =
                                                    let uu____13953 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13954 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13953,
                                                      uu____13954) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13948 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13947 in
                                              quant xy uu____13946 in
                                            (FStar_Parser_Const.op_And,
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
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14002 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14001 in
                                                quant xy uu____14000 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13991) in
                                            let uu____14017 =
                                              let uu____14032 =
                                                let uu____14045 =
                                                  let uu____14054 =
                                                    let uu____14055 =
                                                      let uu____14056 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14056 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14055 in
                                                  quant qx uu____14054 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14045) in
                                              [uu____14032] in
                                            uu____13978 :: uu____14017 in
                                          uu____13924 :: uu____13963 in
                                        uu____13870 :: uu____13909 in
                                      uu____13816 :: uu____13855 in
                                    uu____13762 :: uu____13801 in
                                  uu____13708 :: uu____13747 in
                                uu____13660 :: uu____13693 in
                              uu____13606 :: uu____13645 in
                            uu____13552 :: uu____13591 in
                          uu____13498 :: uu____13537 in
                        uu____13444 :: uu____13483 in
                      uu____13390 :: uu____13429 in
                    uu____13342 :: uu____13375 in
                  uu____13295 :: uu____13327 in
                let mk1 l v1 =
                  let uu____14270 =
                    let uu____14279 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14337  ->
                              match uu____14337 with
                              | (l',uu____14351) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14279
                      (FStar_Option.map
                         (fun uu____14411  ->
                            match uu____14411 with | (uu____14430,b) -> b v1)) in
                  FStar_All.pipe_right uu____14270 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14501  ->
                          match uu____14501 with
                          | (l',uu____14515) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14553 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14553 with
        | (xxsym,xx) ->
            let uu____14560 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14560 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14570 =
                   let uu____14577 =
                     let uu____14578 =
                       let uu____14589 =
                         let uu____14590 =
                           let uu____14595 =
                             let uu____14596 =
                               let uu____14601 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14601) in
                             FStar_SMTEncoding_Util.mkEq uu____14596 in
                           (xx_has_type, uu____14595) in
                         FStar_SMTEncoding_Util.mkImp uu____14590 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14589) in
                     FStar_SMTEncoding_Util.mkForall uu____14578 in
                   let uu____14626 =
                     let uu____14627 =
                       let uu____14628 =
                         let uu____14629 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14629 in
                       Prims.strcat module_name uu____14628 in
                     varops.mk_unique uu____14627 in
                   (uu____14577, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14626) in
                 FStar_SMTEncoding_Util.mkAssume uu____14570)
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
    let uu____14665 =
      let uu____14666 =
        let uu____14673 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14673, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14666 in
    let uu____14676 =
      let uu____14679 =
        let uu____14680 =
          let uu____14687 =
            let uu____14688 =
              let uu____14699 =
                let uu____14700 =
                  let uu____14705 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14705) in
                FStar_SMTEncoding_Util.mkImp uu____14700 in
              ([[typing_pred]], [xx], uu____14699) in
            mkForall_fuel uu____14688 in
          (uu____14687, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14680 in
      [uu____14679] in
    uu____14665 :: uu____14676 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14747 =
      let uu____14748 =
        let uu____14755 =
          let uu____14756 =
            let uu____14767 =
              let uu____14772 =
                let uu____14775 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14775] in
              [uu____14772] in
            let uu____14780 =
              let uu____14781 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14781 tt in
            (uu____14767, [bb], uu____14780) in
          FStar_SMTEncoding_Util.mkForall uu____14756 in
        (uu____14755, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14748 in
    let uu____14802 =
      let uu____14805 =
        let uu____14806 =
          let uu____14813 =
            let uu____14814 =
              let uu____14825 =
                let uu____14826 =
                  let uu____14831 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14831) in
                FStar_SMTEncoding_Util.mkImp uu____14826 in
              ([[typing_pred]], [xx], uu____14825) in
            mkForall_fuel uu____14814 in
          (uu____14813, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14806 in
      [uu____14805] in
    uu____14747 :: uu____14802 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14881 =
        let uu____14882 =
          let uu____14889 =
            let uu____14892 =
              let uu____14895 =
                let uu____14898 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14899 =
                  let uu____14902 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14902] in
                uu____14898 :: uu____14899 in
              tt :: uu____14895 in
            tt :: uu____14892 in
          ("Prims.Precedes", uu____14889) in
        FStar_SMTEncoding_Util.mkApp uu____14882 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14881 in
    let precedes_y_x =
      let uu____14906 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14906 in
    let uu____14909 =
      let uu____14910 =
        let uu____14917 =
          let uu____14918 =
            let uu____14929 =
              let uu____14934 =
                let uu____14937 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14937] in
              [uu____14934] in
            let uu____14942 =
              let uu____14943 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14943 tt in
            (uu____14929, [bb], uu____14942) in
          FStar_SMTEncoding_Util.mkForall uu____14918 in
        (uu____14917, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14910 in
    let uu____14964 =
      let uu____14967 =
        let uu____14968 =
          let uu____14975 =
            let uu____14976 =
              let uu____14987 =
                let uu____14988 =
                  let uu____14993 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14993) in
                FStar_SMTEncoding_Util.mkImp uu____14988 in
              ([[typing_pred]], [xx], uu____14987) in
            mkForall_fuel uu____14976 in
          (uu____14975, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14968 in
      let uu____15018 =
        let uu____15021 =
          let uu____15022 =
            let uu____15029 =
              let uu____15030 =
                let uu____15041 =
                  let uu____15042 =
                    let uu____15047 =
                      let uu____15048 =
                        let uu____15051 =
                          let uu____15054 =
                            let uu____15057 =
                              let uu____15058 =
                                let uu____15063 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15064 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15063, uu____15064) in
                              FStar_SMTEncoding_Util.mkGT uu____15058 in
                            let uu____15065 =
                              let uu____15068 =
                                let uu____15069 =
                                  let uu____15074 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15075 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15074, uu____15075) in
                                FStar_SMTEncoding_Util.mkGTE uu____15069 in
                              let uu____15076 =
                                let uu____15079 =
                                  let uu____15080 =
                                    let uu____15085 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15086 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15085, uu____15086) in
                                  FStar_SMTEncoding_Util.mkLT uu____15080 in
                                [uu____15079] in
                              uu____15068 :: uu____15076 in
                            uu____15057 :: uu____15065 in
                          typing_pred_y :: uu____15054 in
                        typing_pred :: uu____15051 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15048 in
                    (uu____15047, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15042 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15041) in
              mkForall_fuel uu____15030 in
            (uu____15029,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15022 in
        [uu____15021] in
      uu____14967 :: uu____15018 in
    uu____14909 :: uu____14964 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15132 =
      let uu____15133 =
        let uu____15140 =
          let uu____15141 =
            let uu____15152 =
              let uu____15157 =
                let uu____15160 = FStar_SMTEncoding_Term.boxString b in
                [uu____15160] in
              [uu____15157] in
            let uu____15165 =
              let uu____15166 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15166 tt in
            (uu____15152, [bb], uu____15165) in
          FStar_SMTEncoding_Util.mkForall uu____15141 in
        (uu____15140, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15133 in
    let uu____15187 =
      let uu____15190 =
        let uu____15191 =
          let uu____15198 =
            let uu____15199 =
              let uu____15210 =
                let uu____15211 =
                  let uu____15216 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15216) in
                FStar_SMTEncoding_Util.mkImp uu____15211 in
              ([[typing_pred]], [xx], uu____15210) in
            mkForall_fuel uu____15199 in
          (uu____15198, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15191 in
      [uu____15190] in
    uu____15132 :: uu____15187 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15269 =
      let uu____15270 =
        let uu____15277 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15277, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15270 in
    [uu____15269] in
  let mk_and_interp env conj uu____15289 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15314 =
      let uu____15315 =
        let uu____15322 =
          let uu____15323 =
            let uu____15334 =
              let uu____15335 =
                let uu____15340 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15340, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15335 in
            ([[l_and_a_b]], [aa; bb], uu____15334) in
          FStar_SMTEncoding_Util.mkForall uu____15323 in
        (uu____15322, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15315 in
    [uu____15314] in
  let mk_or_interp env disj uu____15378 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15403 =
      let uu____15404 =
        let uu____15411 =
          let uu____15412 =
            let uu____15423 =
              let uu____15424 =
                let uu____15429 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15429, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15424 in
            ([[l_or_a_b]], [aa; bb], uu____15423) in
          FStar_SMTEncoding_Util.mkForall uu____15412 in
        (uu____15411, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15404 in
    [uu____15403] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15492 =
      let uu____15493 =
        let uu____15500 =
          let uu____15501 =
            let uu____15512 =
              let uu____15513 =
                let uu____15518 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15518, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15513 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15512) in
          FStar_SMTEncoding_Util.mkForall uu____15501 in
        (uu____15500, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15493 in
    [uu____15492] in
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
    let uu____15591 =
      let uu____15592 =
        let uu____15599 =
          let uu____15600 =
            let uu____15611 =
              let uu____15612 =
                let uu____15617 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15617, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15612 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15611) in
          FStar_SMTEncoding_Util.mkForall uu____15600 in
        (uu____15599, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15592 in
    [uu____15591] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15688 =
      let uu____15689 =
        let uu____15696 =
          let uu____15697 =
            let uu____15708 =
              let uu____15709 =
                let uu____15714 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15714, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15709 in
            ([[l_imp_a_b]], [aa; bb], uu____15708) in
          FStar_SMTEncoding_Util.mkForall uu____15697 in
        (uu____15696, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15689 in
    [uu____15688] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15777 =
      let uu____15778 =
        let uu____15785 =
          let uu____15786 =
            let uu____15797 =
              let uu____15798 =
                let uu____15803 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15803, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15798 in
            ([[l_iff_a_b]], [aa; bb], uu____15797) in
          FStar_SMTEncoding_Util.mkForall uu____15786 in
        (uu____15785, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15778 in
    [uu____15777] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15855 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15855 in
    let uu____15858 =
      let uu____15859 =
        let uu____15866 =
          let uu____15867 =
            let uu____15878 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15878) in
          FStar_SMTEncoding_Util.mkForall uu____15867 in
        (uu____15866, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15859 in
    [uu____15858] in
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
      let uu____15938 =
        let uu____15945 =
          let uu____15948 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15948] in
        ("Valid", uu____15945) in
      FStar_SMTEncoding_Util.mkApp uu____15938 in
    let uu____15951 =
      let uu____15952 =
        let uu____15959 =
          let uu____15960 =
            let uu____15971 =
              let uu____15972 =
                let uu____15977 =
                  let uu____15978 =
                    let uu____15989 =
                      let uu____15994 =
                        let uu____15997 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15997] in
                      [uu____15994] in
                    let uu____16002 =
                      let uu____16003 =
                        let uu____16008 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16008, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16003 in
                    (uu____15989, [xx1], uu____16002) in
                  FStar_SMTEncoding_Util.mkForall uu____15978 in
                (uu____15977, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15972 in
            ([[l_forall_a_b]], [aa; bb], uu____15971) in
          FStar_SMTEncoding_Util.mkForall uu____15960 in
        (uu____15959, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15952 in
    [uu____15951] in
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
      let uu____16090 =
        let uu____16097 =
          let uu____16100 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16100] in
        ("Valid", uu____16097) in
      FStar_SMTEncoding_Util.mkApp uu____16090 in
    let uu____16103 =
      let uu____16104 =
        let uu____16111 =
          let uu____16112 =
            let uu____16123 =
              let uu____16124 =
                let uu____16129 =
                  let uu____16130 =
                    let uu____16141 =
                      let uu____16146 =
                        let uu____16149 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16149] in
                      [uu____16146] in
                    let uu____16154 =
                      let uu____16155 =
                        let uu____16160 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16160, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16155 in
                    (uu____16141, [xx1], uu____16154) in
                  FStar_SMTEncoding_Util.mkExists uu____16130 in
                (uu____16129, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16124 in
            ([[l_exists_a_b]], [aa; bb], uu____16123) in
          FStar_SMTEncoding_Util.mkForall uu____16112 in
        (uu____16111, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16104 in
    [uu____16103] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16220 =
      let uu____16221 =
        let uu____16228 =
          let uu____16229 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16229 range_ty in
        let uu____16230 = varops.mk_unique "typing_range_const" in
        (uu____16228, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16230) in
      FStar_SMTEncoding_Util.mkAssume uu____16221 in
    [uu____16220] in
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
        let uu____16264 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16264 x1 t in
      let uu____16265 =
        let uu____16276 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16276) in
      FStar_SMTEncoding_Util.mkForall uu____16265 in
    let uu____16299 =
      let uu____16300 =
        let uu____16307 =
          let uu____16308 =
            let uu____16319 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16319) in
          FStar_SMTEncoding_Util.mkForall uu____16308 in
        (uu____16307,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16300 in
    [uu____16299] in
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
          let uu____16643 =
            FStar_Util.find_opt
              (fun uu____16669  ->
                 match uu____16669 with
                 | (l,uu____16681) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16643 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16706,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16742 = encode_function_type_as_formula t env in
        match uu____16742 with
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
              let uu____16782 =
                ((let uu____16785 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16785) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16782
              then
                let uu____16792 = new_term_constant_and_tok_from_lid env lid in
                match uu____16792 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16811 =
                        let uu____16812 = FStar_Syntax_Subst.compress t_norm in
                        uu____16812.FStar_Syntax_Syntax.n in
                      match uu____16811 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16818) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16848  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16853 -> [] in
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
                (let uu____16867 = prims.is lid in
                 if uu____16867
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16875 = prims.mk lid vname in
                   match uu____16875 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16899 =
                      let uu____16910 = curried_arrow_formals_comp t_norm in
                      match uu____16910 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16928 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16928
                            then
                              let uu____16929 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___342_16932 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___342_16932.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___342_16932.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___342_16932.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___342_16932.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___342_16932.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___342_16932.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___342_16932.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___342_16932.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___342_16932.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___342_16932.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___342_16932.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___342_16932.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___342_16932.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___342_16932.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___342_16932.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___342_16932.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___342_16932.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___342_16932.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___342_16932.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___342_16932.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___342_16932.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___342_16932.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___342_16932.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___342_16932.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___342_16932.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___342_16932.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___342_16932.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___342_16932.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___342_16932.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___342_16932.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___342_16932.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___342_16932.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___342_16932.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16929
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16944 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16944)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16899 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16989 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16989 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17010 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___314_17052  ->
                                       match uu___314_17052 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17056 =
                                             FStar_Util.prefix vars in
                                           (match uu____17056 with
                                            | (uu____17077,(xxsym,uu____17079))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17097 =
                                                  let uu____17098 =
                                                    let uu____17105 =
                                                      let uu____17106 =
                                                        let uu____17117 =
                                                          let uu____17118 =
                                                            let uu____17123 =
                                                              let uu____17124
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17124 in
                                                            (vapp,
                                                              uu____17123) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17118 in
                                                        ([[vapp]], vars,
                                                          uu____17117) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17106 in
                                                    (uu____17105,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17098 in
                                                [uu____17097])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17143 =
                                             FStar_Util.prefix vars in
                                           (match uu____17143 with
                                            | (uu____17164,(xxsym,uu____17166))
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
                                                let uu____17189 =
                                                  let uu____17190 =
                                                    let uu____17197 =
                                                      let uu____17198 =
                                                        let uu____17209 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17209) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17198 in
                                                    (uu____17197,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17190 in
                                                [uu____17189])
                                       | uu____17226 -> [])) in
                             let uu____17227 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17227 with
                              | (vars,guards,env',decls1,uu____17254) ->
                                  let uu____17267 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17276 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17276, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17278 =
                                          encode_formula p env' in
                                        (match uu____17278 with
                                         | (g,ds) ->
                                             let uu____17289 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17289,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17267 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17302 =
                                           let uu____17309 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17309) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17302 in
                                       let uu____17318 =
                                         let vname_decl =
                                           let uu____17326 =
                                             let uu____17337 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17347  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17337,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17326 in
                                         let uu____17356 =
                                           let env2 =
                                             let uu___343_17362 = env1 in
                                             {
                                               bindings =
                                                 (uu___343_17362.bindings);
                                               depth = (uu___343_17362.depth);
                                               tcenv = (uu___343_17362.tcenv);
                                               warn = (uu___343_17362.warn);
                                               cache = (uu___343_17362.cache);
                                               nolabels =
                                                 (uu___343_17362.nolabels);
                                               use_zfuel_name =
                                                 (uu___343_17362.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___343_17362.current_module_name)
                                             } in
                                           let uu____17363 =
                                             let uu____17364 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17364 in
                                           if uu____17363
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17356 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17379::uu____17380 ->
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
                                                     let uu____17420 =
                                                       let uu____17431 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17431) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17420 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17458 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17461 =
                                               match formals with
                                               | [] ->
                                                   let uu____17478 =
                                                     let uu____17479 =
                                                       let uu____17482 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17482 in
                                                     push_free_var env1 lid
                                                       vname uu____17479 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17478)
                                               | uu____17487 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17494 =
                                                       let uu____17501 =
                                                         let uu____17502 =
                                                           let uu____17513 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17513) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17502 in
                                                       (uu____17501,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17494 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17461 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17318 with
                                        | (decls2,env2) ->
                                            let uu____17556 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17564 =
                                                encode_term res_t1 env' in
                                              match uu____17564 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17577 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17577, decls) in
                                            (match uu____17556 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17588 =
                                                     let uu____17595 =
                                                       let uu____17596 =
                                                         let uu____17607 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17607) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17596 in
                                                     (uu____17595,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17588 in
                                                 let freshness =
                                                   let uu____17623 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17623
                                                   then
                                                     let uu____17628 =
                                                       let uu____17629 =
                                                         let uu____17640 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17651 =
                                                           varops.next_id () in
                                                         (vname, uu____17640,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17651) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17629 in
                                                     let uu____17654 =
                                                       let uu____17657 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17657] in
                                                     uu____17628 ::
                                                       uu____17654
                                                   else [] in
                                                 let g =
                                                   let uu____17662 =
                                                     let uu____17665 =
                                                       let uu____17668 =
                                                         let uu____17671 =
                                                           let uu____17674 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17674 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17671 in
                                                       FStar_List.append
                                                         decls3 uu____17668 in
                                                     FStar_List.append decls2
                                                       uu____17665 in
                                                   FStar_List.append decls11
                                                     uu____17662 in
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
          let uu____17705 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17705 with
          | FStar_Pervasives_Native.None  ->
              let uu____17742 = encode_free_var false env x t t_norm [] in
              (match uu____17742 with
               | (decls,env1) ->
                   let uu____17769 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17769 with
                    | (n1,x',uu____17796) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17817) ->
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
            let uu____17872 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17872 with
            | (decls,env1) ->
                let uu____17891 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17891
                then
                  let uu____17898 =
                    let uu____17901 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17901 in
                  (uu____17898, env1)
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
             (fun uu____17953  ->
                fun lb  ->
                  match uu____17953 with
                  | (decls,env1) ->
                      let uu____17973 =
                        let uu____17980 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17980
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17973 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18001 = FStar_Syntax_Util.head_and_args t in
    match uu____18001 with
    | (hd1,args) ->
        let uu____18038 =
          let uu____18039 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18039.FStar_Syntax_Syntax.n in
        (match uu____18038 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18043,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18062 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18084  ->
      fun quals  ->
        match uu____18084 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18160 = FStar_Util.first_N nbinders formals in
              match uu____18160 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18241  ->
                         fun uu____18242  ->
                           match (uu____18241, uu____18242) with
                           | ((formal,uu____18260),(binder,uu____18262)) ->
                               let uu____18271 =
                                 let uu____18278 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18278) in
                               FStar_Syntax_Syntax.NT uu____18271) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18286 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18317  ->
                              match uu____18317 with
                              | (x,i) ->
                                  let uu____18328 =
                                    let uu___344_18329 = x in
                                    let uu____18330 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___344_18329.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___344_18329.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18330
                                    } in
                                  (uu____18328, i))) in
                    FStar_All.pipe_right uu____18286
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18348 =
                      let uu____18349 = FStar_Syntax_Subst.compress body in
                      let uu____18350 =
                        let uu____18351 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18351 in
                      FStar_Syntax_Syntax.extend_app_n uu____18349
                        uu____18350 in
                    uu____18348 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18412 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18412
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___345_18415 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___345_18415.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___345_18415.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___345_18415.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___345_18415.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___345_18415.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___345_18415.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___345_18415.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___345_18415.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___345_18415.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___345_18415.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___345_18415.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___345_18415.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___345_18415.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___345_18415.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___345_18415.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___345_18415.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___345_18415.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___345_18415.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___345_18415.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___345_18415.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___345_18415.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___345_18415.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___345_18415.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___345_18415.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___345_18415.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___345_18415.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___345_18415.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___345_18415.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___345_18415.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___345_18415.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___345_18415.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___345_18415.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___345_18415.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18448 = FStar_Syntax_Util.abs_formals e in
                match uu____18448 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18512::uu____18513 ->
                         let uu____18528 =
                           let uu____18529 =
                             let uu____18532 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18532 in
                           uu____18529.FStar_Syntax_Syntax.n in
                         (match uu____18528 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18575 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18575 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18617 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18617
                                   then
                                     let uu____18652 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18652 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18746  ->
                                                   fun uu____18747  ->
                                                     match (uu____18746,
                                                             uu____18747)
                                                     with
                                                     | ((x,uu____18765),
                                                        (b,uu____18767)) ->
                                                         let uu____18776 =
                                                           let uu____18783 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18783) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18776)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18785 =
                                            let uu____18806 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18806) in
                                          (uu____18785, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18874 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18874 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18963) ->
                              let uu____18968 =
                                let uu____18989 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18989 in
                              (uu____18968, true)
                          | uu____19054 when Prims.op_Negation norm1 ->
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
                          | uu____19056 ->
                              let uu____19057 =
                                let uu____19058 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19059 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19058
                                  uu____19059 in
                              failwith uu____19057)
                     | uu____19084 ->
                         let rec aux' t_norm2 =
                           let uu____19109 =
                             let uu____19110 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19110.FStar_Syntax_Syntax.n in
                           match uu____19109 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19151 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19151 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19179 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19179 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19259)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19264 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19320 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19320
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19332 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19426  ->
                            fun lb  ->
                              match uu____19426 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19521 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19521
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19524 =
                                      let uu____19539 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19539
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19524 with
                                    | (tok,decl,env2) ->
                                        let uu____19585 =
                                          let uu____19598 =
                                            let uu____19609 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19609, tok) in
                                          uu____19598 :: toks in
                                        (uu____19585, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19332 with
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
                        | uu____19792 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19800 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19800 vars)
                            else
                              (let uu____19802 =
                                 let uu____19809 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19809) in
                               FStar_SMTEncoding_Util.mkApp uu____19802) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19891;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19893;
                             FStar_Syntax_Syntax.lbeff = uu____19894;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19957 =
                              let uu____19964 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19964 with
                              | (tcenv',uu____19982,e_t) ->
                                  let uu____19988 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19999 -> failwith "Impossible" in
                                  (match uu____19988 with
                                   | (e1,t_norm1) ->
                                       ((let uu___348_20015 = env2 in
                                         {
                                           bindings =
                                             (uu___348_20015.bindings);
                                           depth = (uu___348_20015.depth);
                                           tcenv = tcenv';
                                           warn = (uu___348_20015.warn);
                                           cache = (uu___348_20015.cache);
                                           nolabels =
                                             (uu___348_20015.nolabels);
                                           use_zfuel_name =
                                             (uu___348_20015.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___348_20015.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___348_20015.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19957 with
                             | (env',e1,t_norm1) ->
                                 let uu____20025 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20025 with
                                  | ((binders,body,uu____20046,uu____20047),curry)
                                      ->
                                      ((let uu____20058 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20058
                                        then
                                          let uu____20059 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20060 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20059 uu____20060
                                        else ());
                                       (let uu____20062 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20062 with
                                        | (vars,guards,env'1,binder_decls,uu____20089)
                                            ->
                                            let body1 =
                                              let uu____20103 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20103
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20106 =
                                              let uu____20115 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20115
                                              then
                                                let uu____20126 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20127 =
                                                  encode_formula body1 env'1 in
                                                (uu____20126, uu____20127)
                                              else
                                                (let uu____20137 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20137)) in
                                            (match uu____20106 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20160 =
                                                     let uu____20167 =
                                                       let uu____20168 =
                                                         let uu____20179 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20179) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20168 in
                                                     let uu____20190 =
                                                       let uu____20193 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20193 in
                                                     (uu____20167,
                                                       uu____20190,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20160 in
                                                 let uu____20196 =
                                                   let uu____20199 =
                                                     let uu____20202 =
                                                       let uu____20205 =
                                                         let uu____20208 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20208 in
                                                       FStar_List.append
                                                         decls2 uu____20205 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20202 in
                                                   FStar_List.append decls1
                                                     uu____20199 in
                                                 (uu____20196, env2))))))
                        | uu____20213 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20298 = varops.fresh "fuel" in
                          (uu____20298, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20301 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20389  ->
                                  fun uu____20390  ->
                                    match (uu____20389, uu____20390) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20538 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20538 in
                                        let gtok =
                                          let uu____20540 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20540 in
                                        let env4 =
                                          let uu____20542 =
                                            let uu____20545 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20545 in
                                          push_free_var env3 flid gtok
                                            uu____20542 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20301 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20701 t_norm
                              uu____20703 =
                              match (uu____20701, uu____20703) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20747;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20748;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20776 =
                                    let uu____20783 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20783 with
                                    | (tcenv',uu____20805,e_t) ->
                                        let uu____20811 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20822 ->
                                              failwith "Impossible" in
                                        (match uu____20811 with
                                         | (e1,t_norm1) ->
                                             ((let uu___349_20838 = env3 in
                                               {
                                                 bindings =
                                                   (uu___349_20838.bindings);
                                                 depth =
                                                   (uu___349_20838.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___349_20838.warn);
                                                 cache =
                                                   (uu___349_20838.cache);
                                                 nolabels =
                                                   (uu___349_20838.nolabels);
                                                 use_zfuel_name =
                                                   (uu___349_20838.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___349_20838.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___349_20838.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20776 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20853 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20853
                                         then
                                           let uu____20854 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20855 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20856 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20854 uu____20855
                                             uu____20856
                                         else ());
                                        (let uu____20858 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20858 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20895 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20895
                                               then
                                                 let uu____20896 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20897 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20898 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20899 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20896 uu____20897
                                                   uu____20898 uu____20899
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20903 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20903 with
                                               | (vars,guards,env'1,binder_decls,uu____20934)
                                                   ->
                                                   let decl_g =
                                                     let uu____20948 =
                                                       let uu____20959 =
                                                         let uu____20962 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20962 in
                                                       (g, uu____20959,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20948 in
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
                                                     let uu____20987 =
                                                       let uu____20994 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20994) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20987 in
                                                   let gsapp =
                                                     let uu____21004 =
                                                       let uu____21011 =
                                                         let uu____21014 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21014 ::
                                                           vars_tm in
                                                       (g, uu____21011) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21004 in
                                                   let gmax =
                                                     let uu____21020 =
                                                       let uu____21027 =
                                                         let uu____21030 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21030 ::
                                                           vars_tm in
                                                       (g, uu____21027) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21020 in
                                                   let body1 =
                                                     let uu____21036 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21036
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21038 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21038 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21056 =
                                                            let uu____21063 =
                                                              let uu____21064
                                                                =
                                                                let uu____21079
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
                                                                  uu____21079) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21064 in
                                                            let uu____21100 =
                                                              let uu____21103
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21103 in
                                                            (uu____21063,
                                                              uu____21100,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21056 in
                                                        let eqn_f =
                                                          let uu____21107 =
                                                            let uu____21114 =
                                                              let uu____21115
                                                                =
                                                                let uu____21126
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21126) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21115 in
                                                            (uu____21114,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21107 in
                                                        let eqn_g' =
                                                          let uu____21140 =
                                                            let uu____21147 =
                                                              let uu____21148
                                                                =
                                                                let uu____21159
                                                                  =
                                                                  let uu____21160
                                                                    =
                                                                    let uu____21165
                                                                    =
                                                                    let uu____21166
                                                                    =
                                                                    let uu____21173
                                                                    =
                                                                    let uu____21176
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21176
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21173) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21166 in
                                                                    (gsapp,
                                                                    uu____21165) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21160 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21159) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21148 in
                                                            (uu____21147,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21140 in
                                                        let uu____21199 =
                                                          let uu____21208 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21208
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21237)
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
                                                                  let uu____21262
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21262
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21267
                                                                  =
                                                                  let uu____21274
                                                                    =
                                                                    let uu____21275
                                                                    =
                                                                    let uu____21286
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21286) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21275 in
                                                                  (uu____21274,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21267 in
                                                              let uu____21307
                                                                =
                                                                let uu____21314
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21314
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21327
                                                                    =
                                                                    let uu____21330
                                                                    =
                                                                    let uu____21331
                                                                    =
                                                                    let uu____21338
                                                                    =
                                                                    let uu____21339
                                                                    =
                                                                    let uu____21350
                                                                    =
                                                                    let uu____21351
                                                                    =
                                                                    let uu____21356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21356,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21351 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21350) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21339 in
                                                                    (uu____21338,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21331 in
                                                                    [uu____21330] in
                                                                    (d3,
                                                                    uu____21327) in
                                                              (match uu____21307
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21199
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
                            let uu____21421 =
                              let uu____21434 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21513  ->
                                   fun uu____21514  ->
                                     match (uu____21513, uu____21514) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21669 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21669 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21434 in
                            (match uu____21421 with
                             | (decls2,eqns,env01) ->
                                 let uu____21742 =
                                   let isDeclFun uu___315_21754 =
                                     match uu___315_21754 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21755 -> true
                                     | uu____21766 -> false in
                                   let uu____21767 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21767
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21742 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21807 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___316_21811  ->
                                 match uu___316_21811 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21812 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21818 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21818))) in
                      if uu____21807
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
                   let uu____21870 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21870
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
        let uu____21919 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21919 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21923 = encode_sigelt' env se in
      match uu____21923 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21939 =
                  let uu____21940 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21940 in
                [uu____21939]
            | uu____21941 ->
                let uu____21942 =
                  let uu____21945 =
                    let uu____21946 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21946 in
                  uu____21945 :: g in
                let uu____21947 =
                  let uu____21950 =
                    let uu____21951 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21951 in
                  [uu____21950] in
                FStar_List.append uu____21942 uu____21947 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21964 =
          let uu____21965 = FStar_Syntax_Subst.compress t in
          uu____21965.FStar_Syntax_Syntax.n in
        match uu____21964 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21969)) -> s = "opaque_to_smt"
        | uu____21970 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21975 =
          let uu____21976 = FStar_Syntax_Subst.compress t in
          uu____21976.FStar_Syntax_Syntax.n in
        match uu____21975 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21980)) -> s = "uninterpreted_by_smt"
        | uu____21981 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21986 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21991 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21994 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21997 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22012 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22016 =
            let uu____22017 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22017 Prims.op_Negation in
          if uu____22016
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22043 ->
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
               let uu____22063 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22063 with
               | (aname,atok,env2) ->
                   let uu____22079 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22079 with
                    | (formals,uu____22097) ->
                        let uu____22110 =
                          let uu____22115 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22115 env2 in
                        (match uu____22110 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22127 =
                                 let uu____22128 =
                                   let uu____22139 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22155  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22139,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22128 in
                               [uu____22127;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22168 =
                               let aux uu____22220 uu____22221 =
                                 match (uu____22220, uu____22221) with
                                 | ((bv,uu____22273),(env3,acc_sorts,acc)) ->
                                     let uu____22311 = gen_term_var env3 bv in
                                     (match uu____22311 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22168 with
                              | (uu____22383,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22406 =
                                      let uu____22413 =
                                        let uu____22414 =
                                          let uu____22425 =
                                            let uu____22426 =
                                              let uu____22431 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22431) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22426 in
                                          ([[app]], xs_sorts, uu____22425) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22414 in
                                      (uu____22413,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22406 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22451 =
                                      let uu____22458 =
                                        let uu____22459 =
                                          let uu____22470 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22470) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22459 in
                                      (uu____22458,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22451 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22489 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22489 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22517,uu____22518)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22519 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22519 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22536,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22542 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___317_22546  ->
                      match uu___317_22546 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22547 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22552 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22553 -> false)) in
            Prims.op_Negation uu____22542 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22562 =
               let uu____22569 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22569 env fv t quals in
             match uu____22562 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22584 =
                   let uu____22587 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22587 in
                 (uu____22584, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22595 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22595 with
           | (uu____22604,f1) ->
               let uu____22606 = encode_formula f1 env in
               (match uu____22606 with
                | (f2,decls) ->
                    let g =
                      let uu____22620 =
                        let uu____22621 =
                          let uu____22628 =
                            let uu____22631 =
                              let uu____22632 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22632 in
                            FStar_Pervasives_Native.Some uu____22631 in
                          let uu____22633 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22628, uu____22633) in
                        FStar_SMTEncoding_Util.mkAssume uu____22621 in
                      [uu____22620] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22639) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22651 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22669 =
                       let uu____22672 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22672.FStar_Syntax_Syntax.fv_name in
                     uu____22669.FStar_Syntax_Syntax.v in
                   let uu____22673 =
                     let uu____22674 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22674 in
                   if uu____22673
                   then
                     let val_decl =
                       let uu___352_22702 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___352_22702.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___352_22702.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___352_22702.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22707 = encode_sigelt' env1 val_decl in
                     match uu____22707 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22651 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22735,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22737;
                          FStar_Syntax_Syntax.lbtyp = uu____22738;
                          FStar_Syntax_Syntax.lbeff = uu____22739;
                          FStar_Syntax_Syntax.lbdef = uu____22740;_}::[]),uu____22741)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22760 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22760 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22789 =
                   let uu____22792 =
                     let uu____22793 =
                       let uu____22800 =
                         let uu____22801 =
                           let uu____22812 =
                             let uu____22813 =
                               let uu____22818 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22818) in
                             FStar_SMTEncoding_Util.mkEq uu____22813 in
                           ([[b2t_x]], [xx], uu____22812) in
                         FStar_SMTEncoding_Util.mkForall uu____22801 in
                       (uu____22800,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22793 in
                   [uu____22792] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22789 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22851,uu____22852) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___318_22861  ->
                  match uu___318_22861 with
                  | FStar_Syntax_Syntax.Discriminator uu____22862 -> true
                  | uu____22863 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22866,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22877 =
                     let uu____22878 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22878.FStar_Ident.idText in
                   uu____22877 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___319_22882  ->
                     match uu___319_22882 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22883 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22887) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___320_22904  ->
                  match uu___320_22904 with
                  | FStar_Syntax_Syntax.Projector uu____22905 -> true
                  | uu____22910 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22913 = try_lookup_free_var env l in
          (match uu____22913 with
           | FStar_Pervasives_Native.Some uu____22920 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___353_22924 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___353_22924.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___353_22924.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___353_22924.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22931) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22949) ->
          let uu____22958 = encode_sigelts env ses in
          (match uu____22958 with
           | (g,env1) ->
               let uu____22975 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___321_22998  ->
                         match uu___321_22998 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22999;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23000;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23001;_}
                             -> false
                         | uu____23004 -> true)) in
               (match uu____22975 with
                | (g',inversions) ->
                    let uu____23019 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___322_23040  ->
                              match uu___322_23040 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23041 ->
                                  true
                              | uu____23052 -> false)) in
                    (match uu____23019 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23070,tps,k,uu____23073,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___323_23090  ->
                    match uu___323_23090 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23091 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23100 = c in
              match uu____23100 with
              | (name,args,uu____23105,uu____23106,uu____23107) ->
                  let uu____23112 =
                    let uu____23113 =
                      let uu____23124 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23141  ->
                                match uu____23141 with
                                | (uu____23148,sort,uu____23150) -> sort)) in
                      (name, uu____23124, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23113 in
                  [uu____23112]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23177 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23183 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23183 FStar_Option.isNone)) in
            if uu____23177
            then []
            else
              (let uu____23215 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23215 with
               | (xxsym,xx) ->
                   let uu____23224 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23263  ->
                             fun l  ->
                               match uu____23263 with
                               | (out,decls) ->
                                   let uu____23283 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23283 with
                                    | (uu____23294,data_t) ->
                                        let uu____23296 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23296 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23342 =
                                                 let uu____23343 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23343.FStar_Syntax_Syntax.n in
                                               match uu____23342 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23354,indices) ->
                                                   indices
                                               | uu____23376 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23400  ->
                                                         match uu____23400
                                                         with
                                                         | (x,uu____23406) ->
                                                             let uu____23407
                                                               =
                                                               let uu____23408
                                                                 =
                                                                 let uu____23415
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23415,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23408 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23407)
                                                    env) in
                                             let uu____23418 =
                                               encode_args indices env1 in
                                             (match uu____23418 with
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
                                                      let uu____23444 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23460
                                                                 =
                                                                 let uu____23465
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23465,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23460)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23444
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23468 =
                                                      let uu____23469 =
                                                        let uu____23474 =
                                                          let uu____23475 =
                                                            let uu____23480 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23480,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23475 in
                                                        (out, uu____23474) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23469 in
                                                    (uu____23468,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23224 with
                    | (data_ax,decls) ->
                        let uu____23493 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23493 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23504 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23504 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23508 =
                                 let uu____23515 =
                                   let uu____23516 =
                                     let uu____23527 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23542 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23527,
                                       uu____23542) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23516 in
                                 let uu____23557 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23515,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23557) in
                               FStar_SMTEncoding_Util.mkAssume uu____23508 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23560 =
            let uu____23573 =
              let uu____23574 = FStar_Syntax_Subst.compress k in
              uu____23574.FStar_Syntax_Syntax.n in
            match uu____23573 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23619 -> (tps, k) in
          (match uu____23560 with
           | (formals,res) ->
               let uu____23642 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23642 with
                | (formals1,res1) ->
                    let uu____23653 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23653 with
                     | (vars,guards,env',binder_decls,uu____23678) ->
                         let uu____23691 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23691 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23710 =
                                  let uu____23717 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23717) in
                                FStar_SMTEncoding_Util.mkApp uu____23710 in
                              let uu____23726 =
                                let tname_decl =
                                  let uu____23736 =
                                    let uu____23737 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23769  ->
                                              match uu____23769 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23782 = varops.next_id () in
                                    (tname, uu____23737,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23782, false) in
                                  constructor_or_logic_type_decl uu____23736 in
                                let uu____23791 =
                                  match vars with
                                  | [] ->
                                      let uu____23804 =
                                        let uu____23805 =
                                          let uu____23808 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23808 in
                                        push_free_var env1 t tname
                                          uu____23805 in
                                      ([], uu____23804)
                                  | uu____23815 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23824 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23824 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23838 =
                                          let uu____23845 =
                                            let uu____23846 =
                                              let uu____23861 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23861) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23846 in
                                          (uu____23845,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23838 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23791 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23726 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23901 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23901 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23919 =
                                               let uu____23920 =
                                                 let uu____23927 =
                                                   let uu____23928 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23928 in
                                                 (uu____23927,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23920 in
                                             [uu____23919]
                                           else [] in
                                         let uu____23932 =
                                           let uu____23935 =
                                             let uu____23938 =
                                               let uu____23939 =
                                                 let uu____23946 =
                                                   let uu____23947 =
                                                     let uu____23958 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23958) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23947 in
                                                 (uu____23946,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23939 in
                                             [uu____23938] in
                                           FStar_List.append karr uu____23935 in
                                         FStar_List.append decls1 uu____23932 in
                                   let aux =
                                     let uu____23974 =
                                       let uu____23977 =
                                         inversion_axioms tapp vars in
                                       let uu____23980 =
                                         let uu____23983 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23983] in
                                       FStar_List.append uu____23977
                                         uu____23980 in
                                     FStar_List.append kindingAx uu____23974 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23990,uu____23991,uu____23992,uu____23993,uu____23994)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24002,t,uu____24004,n_tps,uu____24006) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24014 = new_term_constant_and_tok_from_lid env d in
          (match uu____24014 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24031 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24031 with
                | (formals,t_res) ->
                    let uu____24066 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24066 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24080 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24080 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24150 =
                                            mk_term_projector_name d x in
                                          (uu____24150,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24152 =
                                  let uu____24171 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24171, true) in
                                FStar_All.pipe_right uu____24152
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
                              let uu____24210 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24210 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24222::uu____24223 ->
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
                                         let uu____24268 =
                                           let uu____24279 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24279) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24268
                                     | uu____24304 -> tok_typing in
                                   let uu____24313 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24313 with
                                    | (vars',guards',env'',decls_formals,uu____24338)
                                        ->
                                        let uu____24351 =
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
                                        (match uu____24351 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24382 ->
                                                   let uu____24389 =
                                                     let uu____24390 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24390 in
                                                   [uu____24389] in
                                             let encode_elim uu____24400 =
                                               let uu____24401 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24401 with
                                               | (head1,args) ->
                                                   let uu____24444 =
                                                     let uu____24445 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24445.FStar_Syntax_Syntax.n in
                                                   (match uu____24444 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24455;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24456;_},uu____24457)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24463 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24463
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
                                                                 | uu____24506
                                                                    ->
                                                                    let uu____24507
                                                                    =
                                                                    let uu____24512
                                                                    =
                                                                    let uu____24513
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24513 in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____24512) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24507
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24529
                                                                    =
                                                                    let uu____24530
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24530 in
                                                                    if
                                                                    uu____24529
                                                                    then
                                                                    let uu____24543
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24543]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24545
                                                               =
                                                               let uu____24558
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24608
                                                                     ->
                                                                    fun
                                                                    uu____24609
                                                                     ->
                                                                    match 
                                                                    (uu____24608,
                                                                    uu____24609)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24704
                                                                    =
                                                                    let uu____24711
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24711 in
                                                                    (match uu____24704
                                                                    with
                                                                    | 
                                                                    (uu____24724,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24732
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24732
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24734
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
                                                                 uu____24558 in
                                                             (match uu____24545
                                                              with
                                                              | (uu____24749,arg_vars,elim_eqns_or_guards,uu____24752)
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
                                                                    let uu____24782
                                                                    =
                                                                    let uu____24789
                                                                    =
                                                                    let uu____24790
                                                                    =
                                                                    let uu____24801
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24812
                                                                    =
                                                                    let uu____24813
                                                                    =
                                                                    let uu____24818
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24818) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24813 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24801,
                                                                    uu____24812) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24790 in
                                                                    (uu____24789,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24782 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24841
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24841,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24843
                                                                    =
                                                                    let uu____24850
                                                                    =
                                                                    let uu____24851
                                                                    =
                                                                    let uu____24862
                                                                    =
                                                                    let uu____24867
                                                                    =
                                                                    let uu____24870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24870] in
                                                                    [uu____24867] in
                                                                    let uu____24875
                                                                    =
                                                                    let uu____24876
                                                                    =
                                                                    let uu____24881
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24882
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24881,
                                                                    uu____24882) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24876 in
                                                                    (uu____24862,
                                                                    [x],
                                                                    uu____24875) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24851 in
                                                                    let uu____24901
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24850,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24901) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24843
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24908
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
                                                                    (let uu____24936
                                                                    =
                                                                    let uu____24937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24937
                                                                    dapp1 in
                                                                    [uu____24936]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24908
                                                                    FStar_List.flatten in
                                                                    let uu____24944
                                                                    =
                                                                    let uu____24951
                                                                    =
                                                                    let uu____24952
                                                                    =
                                                                    let uu____24963
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24974
                                                                    =
                                                                    let uu____24975
                                                                    =
                                                                    let uu____24980
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24980) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24975 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24963,
                                                                    uu____24974) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24952 in
                                                                    (uu____24951,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24944) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25001 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25001
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
                                                                 | uu____25044
                                                                    ->
                                                                    let uu____25045
                                                                    =
                                                                    let uu____25050
                                                                    =
                                                                    let uu____25051
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25051 in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____25050) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25045
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25067
                                                                    =
                                                                    let uu____25068
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25068 in
                                                                    if
                                                                    uu____25067
                                                                    then
                                                                    let uu____25081
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25081]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25083
                                                               =
                                                               let uu____25096
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25146
                                                                     ->
                                                                    fun
                                                                    uu____25147
                                                                     ->
                                                                    match 
                                                                    (uu____25146,
                                                                    uu____25147)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25242
                                                                    =
                                                                    let uu____25249
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25249 in
                                                                    (match uu____25242
                                                                    with
                                                                    | 
                                                                    (uu____25262,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25270
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25270
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25272
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25272
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
                                                                 uu____25096 in
                                                             (match uu____25083
                                                              with
                                                              | (uu____25287,arg_vars,elim_eqns_or_guards,uu____25290)
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
                                                                    let uu____25320
                                                                    =
                                                                    let uu____25327
                                                                    =
                                                                    let uu____25328
                                                                    =
                                                                    let uu____25339
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25350
                                                                    =
                                                                    let uu____25351
                                                                    =
                                                                    let uu____25356
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25356) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25351 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25339,
                                                                    uu____25350) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25328 in
                                                                    (uu____25327,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25320 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25379
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25379,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25381
                                                                    =
                                                                    let uu____25388
                                                                    =
                                                                    let uu____25389
                                                                    =
                                                                    let uu____25400
                                                                    =
                                                                    let uu____25405
                                                                    =
                                                                    let uu____25408
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25408] in
                                                                    [uu____25405] in
                                                                    let uu____25413
                                                                    =
                                                                    let uu____25414
                                                                    =
                                                                    let uu____25419
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25420
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25419,
                                                                    uu____25420) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25414 in
                                                                    (uu____25400,
                                                                    [x],
                                                                    uu____25413) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25389 in
                                                                    let uu____25439
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25388,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25439) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25381
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25446
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
                                                                    (let uu____25474
                                                                    =
                                                                    let uu____25475
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25475
                                                                    dapp1 in
                                                                    [uu____25474]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25446
                                                                    FStar_List.flatten in
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25489
                                                                    =
                                                                    let uu____25490
                                                                    =
                                                                    let uu____25501
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25512
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    let uu____25518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25518) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25513 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25501,
                                                                    uu____25512) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25490 in
                                                                    (uu____25489,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25482) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25537 ->
                                                        ((let uu____25539 =
                                                            let uu____25544 =
                                                              let uu____25545
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25546
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25545
                                                                uu____25546 in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25544) in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25539);
                                                         ([], []))) in
                                             let uu____25551 = encode_elim () in
                                             (match uu____25551 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25571 =
                                                      let uu____25574 =
                                                        let uu____25577 =
                                                          let uu____25580 =
                                                            let uu____25583 =
                                                              let uu____25584
                                                                =
                                                                let uu____25595
                                                                  =
                                                                  let uu____25598
                                                                    =
                                                                    let uu____25599
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25599 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25598 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25595) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25584 in
                                                            [uu____25583] in
                                                          let uu____25604 =
                                                            let uu____25607 =
                                                              let uu____25610
                                                                =
                                                                let uu____25613
                                                                  =
                                                                  let uu____25616
                                                                    =
                                                                    let uu____25619
                                                                    =
                                                                    let uu____25622
                                                                    =
                                                                    let uu____25623
                                                                    =
                                                                    let uu____25630
                                                                    =
                                                                    let uu____25631
                                                                    =
                                                                    let uu____25642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25642) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25631 in
                                                                    (uu____25630,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25623 in
                                                                    let uu____25655
                                                                    =
                                                                    let uu____25658
                                                                    =
                                                                    let uu____25659
                                                                    =
                                                                    let uu____25666
                                                                    =
                                                                    let uu____25667
                                                                    =
                                                                    let uu____25678
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25689
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25678,
                                                                    uu____25689) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25667 in
                                                                    (uu____25666,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25659 in
                                                                    [uu____25658] in
                                                                    uu____25622
                                                                    ::
                                                                    uu____25655 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25619 in
                                                                  FStar_List.append
                                                                    uu____25616
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25613 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25610 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25607 in
                                                          FStar_List.append
                                                            uu____25580
                                                            uu____25604 in
                                                        FStar_List.append
                                                          decls3 uu____25577 in
                                                      FStar_List.append
                                                        decls2 uu____25574 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25571 in
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
           (fun uu____25735  ->
              fun se  ->
                match uu____25735 with
                | (g,env1) ->
                    let uu____25755 = encode_sigelt env1 se in
                    (match uu____25755 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25812 =
        match uu____25812 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25844 ->
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
                 ((let uu____25850 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25850
                   then
                     let uu____25851 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25852 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25853 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25851 uu____25852 uu____25853
                   else ());
                  (let uu____25855 = encode_term t1 env1 in
                   match uu____25855 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25871 =
                         let uu____25878 =
                           let uu____25879 =
                             let uu____25880 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25880
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25879 in
                         new_term_constant_from_string env1 x uu____25878 in
                       (match uu____25871 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25896 = FStar_Options.log_queries () in
                              if uu____25896
                              then
                                let uu____25899 =
                                  let uu____25900 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25901 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25902 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25900 uu____25901 uu____25902 in
                                FStar_Pervasives_Native.Some uu____25899
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25918,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25932 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25932 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25955,se,uu____25957) ->
                 let uu____25962 = encode_sigelt env1 se in
                 (match uu____25962 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25979,se) ->
                 let uu____25985 = encode_sigelt env1 se in
                 (match uu____25985 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26002 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26002 with | (uu____26025,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26037 'Auu____26038 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26038,'Auu____26037)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26106  ->
              match uu____26106 with
              | (l,uu____26118,uu____26119) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26165  ->
              match uu____26165 with
              | (l,uu____26179,uu____26180) ->
                  let uu____26189 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26190 =
                    let uu____26193 =
                      let uu____26194 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26194 in
                    [uu____26193] in
                  uu____26189 :: uu____26190)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26215 =
      let uu____26218 =
        let uu____26219 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26222 =
          let uu____26223 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26223 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26219;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26222
        } in
      [uu____26218] in
    FStar_ST.op_Colon_Equals last_env uu____26215
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26280 = FStar_ST.op_Bang last_env in
      match uu____26280 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26334 ->
          let uu___354_26337 = e in
          let uu____26338 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___354_26337.bindings);
            depth = (uu___354_26337.depth);
            tcenv;
            warn = (uu___354_26337.warn);
            cache = (uu___354_26337.cache);
            nolabels = (uu___354_26337.nolabels);
            use_zfuel_name = (uu___354_26337.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___354_26337.encode_non_total_function_typ);
            current_module_name = uu____26338
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26342 = FStar_ST.op_Bang last_env in
    match uu____26342 with
    | [] -> failwith "Empty env stack"
    | uu____26395::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26451  ->
    let uu____26452 = FStar_ST.op_Bang last_env in
    match uu____26452 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___355_26513 = hd1 in
          {
            bindings = (uu___355_26513.bindings);
            depth = (uu___355_26513.depth);
            tcenv = (uu___355_26513.tcenv);
            warn = (uu___355_26513.warn);
            cache = refs;
            nolabels = (uu___355_26513.nolabels);
            use_zfuel_name = (uu___355_26513.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___355_26513.encode_non_total_function_typ);
            current_module_name = (uu___355_26513.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26566  ->
    let uu____26567 = FStar_ST.op_Bang last_env in
    match uu____26567 with
    | [] -> failwith "Popping an empty stack"
    | uu____26620::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26711::uu____26712,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___356_26720 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___356_26720.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___356_26720.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___356_26720.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26721 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26736 =
        let uu____26739 =
          let uu____26740 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26740 in
        let uu____26741 = open_fact_db_tags env in uu____26739 :: uu____26741 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26736
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
      let uu____26763 = encode_sigelt env se in
      match uu____26763 with
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
        let uu____26799 = FStar_Options.log_queries () in
        if uu____26799
        then
          let uu____26802 =
            let uu____26803 =
              let uu____26804 =
                let uu____26805 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26805 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26804 in
            FStar_SMTEncoding_Term.Caption uu____26803 in
          uu____26802 :: decls
        else decls in
      (let uu____26816 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26816
       then
         let uu____26817 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26817
       else ());
      (let env =
         let uu____26820 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26820 tcenv in
       let uu____26821 = encode_top_level_facts env se in
       match uu____26821 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26835 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26835)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26847 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26847
       then
         let uu____26848 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26848
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26883  ->
                 fun se  ->
                   match uu____26883 with
                   | (g,env2) ->
                       let uu____26903 = encode_top_level_facts env2 se in
                       (match uu____26903 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26926 =
         encode_signature
           (let uu___357_26935 = env in
            {
              bindings = (uu___357_26935.bindings);
              depth = (uu___357_26935.depth);
              tcenv = (uu___357_26935.tcenv);
              warn = false;
              cache = (uu___357_26935.cache);
              nolabels = (uu___357_26935.nolabels);
              use_zfuel_name = (uu___357_26935.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___357_26935.encode_non_total_function_typ);
              current_module_name = (uu___357_26935.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26926 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26952 = FStar_Options.log_queries () in
             if uu____26952
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___358_26960 = env1 in
               {
                 bindings = (uu___358_26960.bindings);
                 depth = (uu___358_26960.depth);
                 tcenv = (uu___358_26960.tcenv);
                 warn = true;
                 cache = (uu___358_26960.cache);
                 nolabels = (uu___358_26960.nolabels);
                 use_zfuel_name = (uu___358_26960.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___358_26960.encode_non_total_function_typ);
                 current_module_name = (uu___358_26960.current_module_name)
               });
            (let uu____26962 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26962
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
        (let uu____27014 =
           let uu____27015 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27015.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27014);
        (let env =
           let uu____27017 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27017 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27029 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27064 = aux rest in
                 (match uu____27064 with
                  | (out,rest1) ->
                      let t =
                        let uu____27094 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27094 with
                        | FStar_Pervasives_Native.Some uu____27099 ->
                            let uu____27100 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27100
                              x.FStar_Syntax_Syntax.sort
                        | uu____27101 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27105 =
                        let uu____27108 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___359_27111 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___359_27111.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___359_27111.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27108 :: out in
                      (uu____27105, rest1))
             | uu____27116 -> ([], bindings1) in
           let uu____27123 = aux bindings in
           match uu____27123 with
           | (closing,bindings1) ->
               let uu____27148 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27148, bindings1) in
         match uu____27029 with
         | (q1,bindings1) ->
             let uu____27171 =
               let uu____27176 =
                 FStar_List.filter
                   (fun uu___324_27181  ->
                      match uu___324_27181 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27182 ->
                          false
                      | uu____27189 -> true) bindings1 in
               encode_env_bindings env uu____27176 in
             (match uu____27171 with
              | (env_decls,env1) ->
                  ((let uu____27207 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27207
                    then
                      let uu____27208 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27208
                    else ());
                   (let uu____27210 = encode_formula q1 env1 in
                    match uu____27210 with
                    | (phi,qdecls) ->
                        let uu____27231 =
                          let uu____27236 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27236 phi in
                        (match uu____27231 with
                         | (labels,phi1) ->
                             let uu____27253 = encode_labels labels in
                             (match uu____27253 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27290 =
                                      let uu____27297 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27298 =
                                        varops.mk_unique "@query" in
                                      (uu____27297,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27298) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27290 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))