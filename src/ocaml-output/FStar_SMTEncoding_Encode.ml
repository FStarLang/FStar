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
      (fun uu___301_107  ->
         match uu___301_107 with
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
        let uu___324_205 = a in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___324_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___324_205.FStar_Syntax_Syntax.sort)
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
    let uu___325_1849 = x in
    let uu____1850 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1850;
      FStar_Syntax_Syntax.index = (uu___325_1849.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___325_1849.FStar_Syntax_Syntax.sort)
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
                 (fun uu___302_2297  ->
                    match uu___302_2297 with
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
           (fun uu___303_2320  ->
              match uu___303_2320 with
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
        (let uu___326_2400 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___326_2400.tcenv);
           warn = (uu___326_2400.warn);
           cache = (uu___326_2400.cache);
           nolabels = (uu___326_2400.nolabels);
           use_zfuel_name = (uu___326_2400.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___326_2400.encode_non_total_function_typ);
           current_module_name = (uu___326_2400.current_module_name)
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
        (let uu___327_2418 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___327_2418.depth);
           tcenv = (uu___327_2418.tcenv);
           warn = (uu___327_2418.warn);
           cache = (uu___327_2418.cache);
           nolabels = (uu___327_2418.nolabels);
           use_zfuel_name = (uu___327_2418.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___327_2418.encode_non_total_function_typ);
           current_module_name = (uu___327_2418.current_module_name)
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
          (let uu___328_2439 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___328_2439.depth);
             tcenv = (uu___328_2439.tcenv);
             warn = (uu___328_2439.warn);
             cache = (uu___328_2439.cache);
             nolabels = (uu___328_2439.nolabels);
             use_zfuel_name = (uu___328_2439.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___328_2439.encode_non_total_function_typ);
             current_module_name = (uu___328_2439.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___329_2449 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___329_2449.depth);
          tcenv = (uu___329_2449.tcenv);
          warn = (uu___329_2449.warn);
          cache = (uu___329_2449.cache);
          nolabels = (uu___329_2449.nolabels);
          use_zfuel_name = (uu___329_2449.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___329_2449.encode_non_total_function_typ);
          current_module_name = (uu___329_2449.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___304_2473  ->
             match uu___304_2473 with
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
        let uu___330_2544 = env in
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
          depth = (uu___330_2544.depth);
          tcenv = (uu___330_2544.tcenv);
          warn = (uu___330_2544.warn);
          cache = (uu___330_2544.cache);
          nolabels = (uu___330_2544.nolabels);
          use_zfuel_name = (uu___330_2544.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___330_2544.encode_non_total_function_typ);
          current_module_name = (uu___330_2544.current_module_name)
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
        (fun uu___305_2607  ->
           match uu___305_2607 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2646 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2663 =
        lookup_binding env
          (fun uu___306_2671  ->
             match uu___306_2671 with
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
          let uu___331_2787 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___331_2787.depth);
            tcenv = (uu___331_2787.tcenv);
            warn = (uu___331_2787.warn);
            cache = (uu___331_2787.cache);
            nolabels = (uu___331_2787.nolabels);
            use_zfuel_name = (uu___331_2787.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___331_2787.encode_non_total_function_typ);
            current_module_name = (uu___331_2787.current_module_name)
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
            let uu___332_2839 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___332_2839.depth);
              tcenv = (uu___332_2839.tcenv);
              warn = (uu___332_2839.warn);
              cache = (uu___332_2839.cache);
              nolabels = (uu___332_2839.nolabels);
              use_zfuel_name = (uu___332_2839.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___332_2839.encode_non_total_function_typ);
              current_module_name = (uu___332_2839.current_module_name)
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
        (fun uu___307_3083  ->
           match uu___307_3083 with
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
               (fun uu___308_3402  ->
                  match uu___308_3402 with
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
  fun uu___309_3500  ->
    match uu___309_3500 with
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
              ("FStar.Char.char_of_int", uu____4340) in
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
                           (let uu___333_6222 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___333_6222.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___333_6222.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___333_6222.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___333_6222.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___333_6222.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___333_6222.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___333_6222.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___333_6222.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___333_6222.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___333_6222.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___333_6222.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___333_6222.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___333_6222.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___333_6222.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___333_6222.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___333_6222.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___333_6222.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___333_6222.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___333_6222.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___333_6222.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___333_6222.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___333_6222.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___333_6222.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___333_6222.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___333_6222.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___333_6222.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___333_6222.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___333_6222.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___333_6222.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___333_6222.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___333_6222.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___333_6222.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___333_6222.FStar_TypeChecker_Env.dep_graph)
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
            let uu___334_10363 = env in
            {
              bindings = (uu___334_10363.bindings);
              depth = (uu___334_10363.depth);
              tcenv = (uu___334_10363.tcenv);
              warn = (uu___334_10363.warn);
              cache = (uu___334_10363.cache);
              nolabels = (uu___334_10363.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___334_10363.encode_non_total_function_typ);
              current_module_name = (uu___334_10363.current_module_name)
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
                      let uu___335_10580 = env2 in
                      {
                        bindings = (uu___335_10580.bindings);
                        depth = (uu___335_10580.depth);
                        tcenv = (uu___335_10580.tcenv);
                        warn = (uu___335_10580.warn);
                        cache = (uu___335_10580.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___335_10580.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___335_10580.encode_non_total_function_typ);
                        current_module_name =
                          (uu___335_10580.current_module_name)
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
              let uu___336_10738 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___336_10738.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___336_10738.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10737, decls) in
      let const_op f r uu____10769 =
        let uu____10782 = f r in (uu____10782, []) in
      let un_op f l =
        let uu____10801 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10801 in
      let bin_op f uu___310_10817 =
        match uu___310_10817 with
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
              let uu___337_10930 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___337_10930.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___337_10930.FStar_SMTEncoding_Term.freevars);
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
      let mk_imp1 r uu___311_11065 =
        match uu___311_11065 with
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
      let mk_ite r uu___312_11156 =
        match uu___312_11156 with
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
             | uu____12078 when head_redex env head2 ->
                 let uu____12091 = whnf env phi1 in
                 encode_formula uu____12091 env
             | uu____12092 ->
                 let uu____12105 = encode_term phi1 env in
                 (match uu____12105 with
                  | (tt,decls) ->
                      let uu____12116 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___338_12119 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___338_12119.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___338_12119.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12116, decls)))
        | uu____12120 ->
            let uu____12121 = encode_term phi1 env in
            (match uu____12121 with
             | (tt,decls) ->
                 let uu____12132 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___339_12135 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___339_12135.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___339_12135.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12132, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12171 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12171 with
        | (vars,guards,env2,decls,uu____12210) ->
            let uu____12223 =
              let uu____12236 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12284 =
                          let uu____12293 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12323  ->
                                    match uu____12323 with
                                    | (t,uu____12333) ->
                                        encode_term t
                                          (let uu___340_12335 = env2 in
                                           {
                                             bindings =
                                               (uu___340_12335.bindings);
                                             depth = (uu___340_12335.depth);
                                             tcenv = (uu___340_12335.tcenv);
                                             warn = (uu___340_12335.warn);
                                             cache = (uu___340_12335.cache);
                                             nolabels =
                                               (uu___340_12335.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___340_12335.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___340_12335.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12293 FStar_List.unzip in
                        match uu____12284 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12236 FStar_List.unzip in
            (match uu____12223 with
             | (pats,decls') ->
                 let uu____12434 = encode_formula body env2 in
                 (match uu____12434 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12466;
                             FStar_SMTEncoding_Term.rng = uu____12467;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12482 -> guards in
                      let uu____12487 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12487, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12547  ->
                   match uu____12547 with
                   | (x,uu____12553) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12561 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12573 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12573) uu____12561 tl1 in
             let uu____12576 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12603  ->
                       match uu____12603 with
                       | (b,uu____12609) ->
                           let uu____12610 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12610)) in
             (match uu____12576 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12616) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12630 =
                    let uu____12631 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12631 in
                  FStar_Errors.warn pos uu____12630) in
       let uu____12632 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12632 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12641 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12699  ->
                     match uu____12699 with
                     | (l,uu____12713) -> FStar_Ident.lid_equals op l)) in
           (match uu____12641 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12746,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12786 = encode_q_body env vars pats body in
             match uu____12786 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12831 =
                     let uu____12842 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12842) in
                   FStar_SMTEncoding_Term.mkForall uu____12831
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12861 = encode_q_body env vars pats body in
             match uu____12861 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12905 =
                   let uu____12906 =
                     let uu____12917 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12917) in
                   FStar_SMTEncoding_Term.mkExists uu____12906
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12905, decls))))
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
  let uu____13010 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13010 with
  | (asym,a) ->
      let uu____13017 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13017 with
       | (xsym,x) ->
           let uu____13024 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13024 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13068 =
                      let uu____13079 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13079, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13068 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13105 =
                      let uu____13112 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13112) in
                    FStar_SMTEncoding_Util.mkApp uu____13105 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13125 =
                    let uu____13128 =
                      let uu____13131 =
                        let uu____13134 =
                          let uu____13135 =
                            let uu____13142 =
                              let uu____13143 =
                                let uu____13154 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13154) in
                              FStar_SMTEncoding_Util.mkForall uu____13143 in
                            (uu____13142, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13135 in
                        let uu____13171 =
                          let uu____13174 =
                            let uu____13175 =
                              let uu____13182 =
                                let uu____13183 =
                                  let uu____13194 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13194) in
                                FStar_SMTEncoding_Util.mkForall uu____13183 in
                              (uu____13182,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13175 in
                          [uu____13174] in
                        uu____13134 :: uu____13171 in
                      xtok_decl :: uu____13131 in
                    xname_decl :: uu____13128 in
                  (xtok1, uu____13125) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13285 =
                    let uu____13298 =
                      let uu____13307 =
                        let uu____13308 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13308 in
                      quant axy uu____13307 in
                    (FStar_Parser_Const.op_Eq, uu____13298) in
                  let uu____13317 =
                    let uu____13332 =
                      let uu____13345 =
                        let uu____13354 =
                          let uu____13355 =
                            let uu____13356 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13356 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13355 in
                        quant axy uu____13354 in
                      (FStar_Parser_Const.op_notEq, uu____13345) in
                    let uu____13365 =
                      let uu____13380 =
                        let uu____13393 =
                          let uu____13402 =
                            let uu____13403 =
                              let uu____13404 =
                                let uu____13409 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13410 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13409, uu____13410) in
                              FStar_SMTEncoding_Util.mkLT uu____13404 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13403 in
                          quant xy uu____13402 in
                        (FStar_Parser_Const.op_LT, uu____13393) in
                      let uu____13419 =
                        let uu____13434 =
                          let uu____13447 =
                            let uu____13456 =
                              let uu____13457 =
                                let uu____13458 =
                                  let uu____13463 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13464 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13463, uu____13464) in
                                FStar_SMTEncoding_Util.mkLTE uu____13458 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13457 in
                            quant xy uu____13456 in
                          (FStar_Parser_Const.op_LTE, uu____13447) in
                        let uu____13473 =
                          let uu____13488 =
                            let uu____13501 =
                              let uu____13510 =
                                let uu____13511 =
                                  let uu____13512 =
                                    let uu____13517 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13518 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13517, uu____13518) in
                                  FStar_SMTEncoding_Util.mkGT uu____13512 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13511 in
                              quant xy uu____13510 in
                            (FStar_Parser_Const.op_GT, uu____13501) in
                          let uu____13527 =
                            let uu____13542 =
                              let uu____13555 =
                                let uu____13564 =
                                  let uu____13565 =
                                    let uu____13566 =
                                      let uu____13571 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13572 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13571, uu____13572) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13566 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13565 in
                                quant xy uu____13564 in
                              (FStar_Parser_Const.op_GTE, uu____13555) in
                            let uu____13581 =
                              let uu____13596 =
                                let uu____13609 =
                                  let uu____13618 =
                                    let uu____13619 =
                                      let uu____13620 =
                                        let uu____13625 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13626 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13625, uu____13626) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13620 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13619 in
                                  quant xy uu____13618 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13609) in
                              let uu____13635 =
                                let uu____13650 =
                                  let uu____13663 =
                                    let uu____13672 =
                                      let uu____13673 =
                                        let uu____13674 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13674 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13673 in
                                    quant qx uu____13672 in
                                  (FStar_Parser_Const.op_Minus, uu____13663) in
                                let uu____13683 =
                                  let uu____13698 =
                                    let uu____13711 =
                                      let uu____13720 =
                                        let uu____13721 =
                                          let uu____13722 =
                                            let uu____13727 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13728 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13727, uu____13728) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13722 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13721 in
                                      quant xy uu____13720 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13711) in
                                  let uu____13737 =
                                    let uu____13752 =
                                      let uu____13765 =
                                        let uu____13774 =
                                          let uu____13775 =
                                            let uu____13776 =
                                              let uu____13781 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13782 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13781, uu____13782) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13776 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13775 in
                                        quant xy uu____13774 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13765) in
                                    let uu____13791 =
                                      let uu____13806 =
                                        let uu____13819 =
                                          let uu____13828 =
                                            let uu____13829 =
                                              let uu____13830 =
                                                let uu____13835 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13836 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13835, uu____13836) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13830 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13829 in
                                          quant xy uu____13828 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13819) in
                                      let uu____13845 =
                                        let uu____13860 =
                                          let uu____13873 =
                                            let uu____13882 =
                                              let uu____13883 =
                                                let uu____13884 =
                                                  let uu____13889 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13890 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13889, uu____13890) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13884 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13883 in
                                            quant xy uu____13882 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13873) in
                                        let uu____13899 =
                                          let uu____13914 =
                                            let uu____13927 =
                                              let uu____13936 =
                                                let uu____13937 =
                                                  let uu____13938 =
                                                    let uu____13943 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13944 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13943,
                                                      uu____13944) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13938 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13937 in
                                              quant xy uu____13936 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13927) in
                                          let uu____13953 =
                                            let uu____13968 =
                                              let uu____13981 =
                                                let uu____13990 =
                                                  let uu____13991 =
                                                    let uu____13992 =
                                                      let uu____13997 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____13998 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____13997,
                                                        uu____13998) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13992 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13991 in
                                                quant xy uu____13990 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13981) in
                                            let uu____14007 =
                                              let uu____14022 =
                                                let uu____14035 =
                                                  let uu____14044 =
                                                    let uu____14045 =
                                                      let uu____14046 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14046 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14045 in
                                                  quant qx uu____14044 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14035) in
                                              [uu____14022] in
                                            uu____13968 :: uu____14007 in
                                          uu____13914 :: uu____13953 in
                                        uu____13860 :: uu____13899 in
                                      uu____13806 :: uu____13845 in
                                    uu____13752 :: uu____13791 in
                                  uu____13698 :: uu____13737 in
                                uu____13650 :: uu____13683 in
                              uu____13596 :: uu____13635 in
                            uu____13542 :: uu____13581 in
                          uu____13488 :: uu____13527 in
                        uu____13434 :: uu____13473 in
                      uu____13380 :: uu____13419 in
                    uu____13332 :: uu____13365 in
                  uu____13285 :: uu____13317 in
                let mk1 l v1 =
                  let uu____14260 =
                    let uu____14269 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14327  ->
                              match uu____14327 with
                              | (l',uu____14341) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14269
                      (FStar_Option.map
                         (fun uu____14401  ->
                            match uu____14401 with | (uu____14420,b) -> b v1)) in
                  FStar_All.pipe_right uu____14260 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14491  ->
                          match uu____14491 with
                          | (l',uu____14505) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14543 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14543 with
        | (xxsym,xx) ->
            let uu____14550 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14550 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14560 =
                   let uu____14567 =
                     let uu____14568 =
                       let uu____14579 =
                         let uu____14580 =
                           let uu____14585 =
                             let uu____14586 =
                               let uu____14591 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14591) in
                             FStar_SMTEncoding_Util.mkEq uu____14586 in
                           (xx_has_type, uu____14585) in
                         FStar_SMTEncoding_Util.mkImp uu____14580 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14579) in
                     FStar_SMTEncoding_Util.mkForall uu____14568 in
                   let uu____14616 =
                     let uu____14617 =
                       let uu____14618 =
                         let uu____14619 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14619 in
                       Prims.strcat module_name uu____14618 in
                     varops.mk_unique uu____14617 in
                   (uu____14567, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14616) in
                 FStar_SMTEncoding_Util.mkAssume uu____14560)
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
    let uu____14655 =
      let uu____14656 =
        let uu____14663 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14663, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14656 in
    let uu____14666 =
      let uu____14669 =
        let uu____14670 =
          let uu____14677 =
            let uu____14678 =
              let uu____14689 =
                let uu____14690 =
                  let uu____14695 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14695) in
                FStar_SMTEncoding_Util.mkImp uu____14690 in
              ([[typing_pred]], [xx], uu____14689) in
            mkForall_fuel uu____14678 in
          (uu____14677, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14670 in
      [uu____14669] in
    uu____14655 :: uu____14666 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14737 =
      let uu____14738 =
        let uu____14745 =
          let uu____14746 =
            let uu____14757 =
              let uu____14762 =
                let uu____14765 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14765] in
              [uu____14762] in
            let uu____14770 =
              let uu____14771 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14771 tt in
            (uu____14757, [bb], uu____14770) in
          FStar_SMTEncoding_Util.mkForall uu____14746 in
        (uu____14745, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14738 in
    let uu____14792 =
      let uu____14795 =
        let uu____14796 =
          let uu____14803 =
            let uu____14804 =
              let uu____14815 =
                let uu____14816 =
                  let uu____14821 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14821) in
                FStar_SMTEncoding_Util.mkImp uu____14816 in
              ([[typing_pred]], [xx], uu____14815) in
            mkForall_fuel uu____14804 in
          (uu____14803, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14796 in
      [uu____14795] in
    uu____14737 :: uu____14792 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14871 =
        let uu____14872 =
          let uu____14879 =
            let uu____14882 =
              let uu____14885 =
                let uu____14888 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14889 =
                  let uu____14892 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14892] in
                uu____14888 :: uu____14889 in
              tt :: uu____14885 in
            tt :: uu____14882 in
          ("Prims.Precedes", uu____14879) in
        FStar_SMTEncoding_Util.mkApp uu____14872 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14871 in
    let precedes_y_x =
      let uu____14896 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14896 in
    let uu____14899 =
      let uu____14900 =
        let uu____14907 =
          let uu____14908 =
            let uu____14919 =
              let uu____14924 =
                let uu____14927 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14927] in
              [uu____14924] in
            let uu____14932 =
              let uu____14933 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14933 tt in
            (uu____14919, [bb], uu____14932) in
          FStar_SMTEncoding_Util.mkForall uu____14908 in
        (uu____14907, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14900 in
    let uu____14954 =
      let uu____14957 =
        let uu____14958 =
          let uu____14965 =
            let uu____14966 =
              let uu____14977 =
                let uu____14978 =
                  let uu____14983 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14983) in
                FStar_SMTEncoding_Util.mkImp uu____14978 in
              ([[typing_pred]], [xx], uu____14977) in
            mkForall_fuel uu____14966 in
          (uu____14965, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14958 in
      let uu____15008 =
        let uu____15011 =
          let uu____15012 =
            let uu____15019 =
              let uu____15020 =
                let uu____15031 =
                  let uu____15032 =
                    let uu____15037 =
                      let uu____15038 =
                        let uu____15041 =
                          let uu____15044 =
                            let uu____15047 =
                              let uu____15048 =
                                let uu____15053 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15054 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15053, uu____15054) in
                              FStar_SMTEncoding_Util.mkGT uu____15048 in
                            let uu____15055 =
                              let uu____15058 =
                                let uu____15059 =
                                  let uu____15064 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15065 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15064, uu____15065) in
                                FStar_SMTEncoding_Util.mkGTE uu____15059 in
                              let uu____15066 =
                                let uu____15069 =
                                  let uu____15070 =
                                    let uu____15075 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15076 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15075, uu____15076) in
                                  FStar_SMTEncoding_Util.mkLT uu____15070 in
                                [uu____15069] in
                              uu____15058 :: uu____15066 in
                            uu____15047 :: uu____15055 in
                          typing_pred_y :: uu____15044 in
                        typing_pred :: uu____15041 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15038 in
                    (uu____15037, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15032 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15031) in
              mkForall_fuel uu____15020 in
            (uu____15019,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15012 in
        [uu____15011] in
      uu____14957 :: uu____15008 in
    uu____14899 :: uu____14954 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15122 =
      let uu____15123 =
        let uu____15130 =
          let uu____15131 =
            let uu____15142 =
              let uu____15147 =
                let uu____15150 = FStar_SMTEncoding_Term.boxString b in
                [uu____15150] in
              [uu____15147] in
            let uu____15155 =
              let uu____15156 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15156 tt in
            (uu____15142, [bb], uu____15155) in
          FStar_SMTEncoding_Util.mkForall uu____15131 in
        (uu____15130, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15123 in
    let uu____15177 =
      let uu____15180 =
        let uu____15181 =
          let uu____15188 =
            let uu____15189 =
              let uu____15200 =
                let uu____15201 =
                  let uu____15206 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15206) in
                FStar_SMTEncoding_Util.mkImp uu____15201 in
              ([[typing_pred]], [xx], uu____15200) in
            mkForall_fuel uu____15189 in
          (uu____15188, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15181 in
      [uu____15180] in
    uu____15122 :: uu____15177 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15259 =
      let uu____15260 =
        let uu____15267 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15267, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15260 in
    [uu____15259] in
  let mk_and_interp env conj uu____15279 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15304 =
      let uu____15305 =
        let uu____15312 =
          let uu____15313 =
            let uu____15324 =
              let uu____15325 =
                let uu____15330 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15330, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15325 in
            ([[l_and_a_b]], [aa; bb], uu____15324) in
          FStar_SMTEncoding_Util.mkForall uu____15313 in
        (uu____15312, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15305 in
    [uu____15304] in
  let mk_or_interp env disj uu____15368 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15393 =
      let uu____15394 =
        let uu____15401 =
          let uu____15402 =
            let uu____15413 =
              let uu____15414 =
                let uu____15419 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15419, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15414 in
            ([[l_or_a_b]], [aa; bb], uu____15413) in
          FStar_SMTEncoding_Util.mkForall uu____15402 in
        (uu____15401, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15394 in
    [uu____15393] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15482 =
      let uu____15483 =
        let uu____15490 =
          let uu____15491 =
            let uu____15502 =
              let uu____15503 =
                let uu____15508 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15508, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15503 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15502) in
          FStar_SMTEncoding_Util.mkForall uu____15491 in
        (uu____15490, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15483 in
    [uu____15482] in
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
    let uu____15581 =
      let uu____15582 =
        let uu____15589 =
          let uu____15590 =
            let uu____15601 =
              let uu____15602 =
                let uu____15607 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15607, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15602 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15601) in
          FStar_SMTEncoding_Util.mkForall uu____15590 in
        (uu____15589, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15582 in
    [uu____15581] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15678 =
      let uu____15679 =
        let uu____15686 =
          let uu____15687 =
            let uu____15698 =
              let uu____15699 =
                let uu____15704 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15704, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15699 in
            ([[l_imp_a_b]], [aa; bb], uu____15698) in
          FStar_SMTEncoding_Util.mkForall uu____15687 in
        (uu____15686, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15679 in
    [uu____15678] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15767 =
      let uu____15768 =
        let uu____15775 =
          let uu____15776 =
            let uu____15787 =
              let uu____15788 =
                let uu____15793 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15793, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15788 in
            ([[l_iff_a_b]], [aa; bb], uu____15787) in
          FStar_SMTEncoding_Util.mkForall uu____15776 in
        (uu____15775, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15768 in
    [uu____15767] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15845 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15845 in
    let uu____15848 =
      let uu____15849 =
        let uu____15856 =
          let uu____15857 =
            let uu____15868 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15868) in
          FStar_SMTEncoding_Util.mkForall uu____15857 in
        (uu____15856, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15849 in
    [uu____15848] in
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
      let uu____15928 =
        let uu____15935 =
          let uu____15938 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15938] in
        ("Valid", uu____15935) in
      FStar_SMTEncoding_Util.mkApp uu____15928 in
    let uu____15941 =
      let uu____15942 =
        let uu____15949 =
          let uu____15950 =
            let uu____15961 =
              let uu____15962 =
                let uu____15967 =
                  let uu____15968 =
                    let uu____15979 =
                      let uu____15984 =
                        let uu____15987 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15987] in
                      [uu____15984] in
                    let uu____15992 =
                      let uu____15993 =
                        let uu____15998 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15998, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15993 in
                    (uu____15979, [xx1], uu____15992) in
                  FStar_SMTEncoding_Util.mkForall uu____15968 in
                (uu____15967, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15962 in
            ([[l_forall_a_b]], [aa; bb], uu____15961) in
          FStar_SMTEncoding_Util.mkForall uu____15950 in
        (uu____15949, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15942 in
    [uu____15941] in
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
      let uu____16080 =
        let uu____16087 =
          let uu____16090 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16090] in
        ("Valid", uu____16087) in
      FStar_SMTEncoding_Util.mkApp uu____16080 in
    let uu____16093 =
      let uu____16094 =
        let uu____16101 =
          let uu____16102 =
            let uu____16113 =
              let uu____16114 =
                let uu____16119 =
                  let uu____16120 =
                    let uu____16131 =
                      let uu____16136 =
                        let uu____16139 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16139] in
                      [uu____16136] in
                    let uu____16144 =
                      let uu____16145 =
                        let uu____16150 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16150, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16145 in
                    (uu____16131, [xx1], uu____16144) in
                  FStar_SMTEncoding_Util.mkExists uu____16120 in
                (uu____16119, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16114 in
            ([[l_exists_a_b]], [aa; bb], uu____16113) in
          FStar_SMTEncoding_Util.mkForall uu____16102 in
        (uu____16101, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16094 in
    [uu____16093] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16210 =
      let uu____16211 =
        let uu____16218 =
          let uu____16219 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16219 range_ty in
        let uu____16220 = varops.mk_unique "typing_range_const" in
        (uu____16218, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16220) in
      FStar_SMTEncoding_Util.mkAssume uu____16211 in
    [uu____16210] in
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
        let uu____16254 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16254 x1 t in
      let uu____16255 =
        let uu____16266 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16266) in
      FStar_SMTEncoding_Util.mkForall uu____16255 in
    let uu____16289 =
      let uu____16290 =
        let uu____16297 =
          let uu____16298 =
            let uu____16309 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16309) in
          FStar_SMTEncoding_Util.mkForall uu____16298 in
        (uu____16297,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16290 in
    [uu____16289] in
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
          let uu____16633 =
            FStar_Util.find_opt
              (fun uu____16659  ->
                 match uu____16659 with
                 | (l,uu____16671) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16633 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16696,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16732 = encode_function_type_as_formula t env in
        match uu____16732 with
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
              let uu____16772 =
                ((let uu____16775 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16775) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16772
              then
                let uu____16782 = new_term_constant_and_tok_from_lid env lid in
                match uu____16782 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16801 =
                        let uu____16802 = FStar_Syntax_Subst.compress t_norm in
                        uu____16802.FStar_Syntax_Syntax.n in
                      match uu____16801 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16808) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16838  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16843 -> [] in
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
                (let uu____16857 = prims.is lid in
                 if uu____16857
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16865 = prims.mk lid vname in
                   match uu____16865 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16889 =
                      let uu____16900 = curried_arrow_formals_comp t_norm in
                      match uu____16900 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16918 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16918
                            then
                              let uu____16919 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___341_16922 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___341_16922.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___341_16922.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___341_16922.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___341_16922.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___341_16922.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___341_16922.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___341_16922.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___341_16922.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___341_16922.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___341_16922.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___341_16922.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___341_16922.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___341_16922.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___341_16922.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___341_16922.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___341_16922.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___341_16922.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___341_16922.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___341_16922.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___341_16922.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___341_16922.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___341_16922.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___341_16922.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___341_16922.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___341_16922.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___341_16922.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___341_16922.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___341_16922.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___341_16922.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___341_16922.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___341_16922.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___341_16922.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___341_16922.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16919
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16934 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16934)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16889 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16979 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16979 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17000 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___313_17042  ->
                                       match uu___313_17042 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17046 =
                                             FStar_Util.prefix vars in
                                           (match uu____17046 with
                                            | (uu____17067,(xxsym,uu____17069))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17087 =
                                                  let uu____17088 =
                                                    let uu____17095 =
                                                      let uu____17096 =
                                                        let uu____17107 =
                                                          let uu____17108 =
                                                            let uu____17113 =
                                                              let uu____17114
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17114 in
                                                            (vapp,
                                                              uu____17113) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17108 in
                                                        ([[vapp]], vars,
                                                          uu____17107) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17096 in
                                                    (uu____17095,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17088 in
                                                [uu____17087])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17133 =
                                             FStar_Util.prefix vars in
                                           (match uu____17133 with
                                            | (uu____17154,(xxsym,uu____17156))
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
                                                let uu____17179 =
                                                  let uu____17180 =
                                                    let uu____17187 =
                                                      let uu____17188 =
                                                        let uu____17199 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17199) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17188 in
                                                    (uu____17187,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17180 in
                                                [uu____17179])
                                       | uu____17216 -> [])) in
                             let uu____17217 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17217 with
                              | (vars,guards,env',decls1,uu____17244) ->
                                  let uu____17257 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17266 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17266, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17268 =
                                          encode_formula p env' in
                                        (match uu____17268 with
                                         | (g,ds) ->
                                             let uu____17279 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17279,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17257 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17292 =
                                           let uu____17299 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17299) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17292 in
                                       let uu____17308 =
                                         let vname_decl =
                                           let uu____17316 =
                                             let uu____17327 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17337  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17327,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17316 in
                                         let uu____17346 =
                                           let env2 =
                                             let uu___342_17352 = env1 in
                                             {
                                               bindings =
                                                 (uu___342_17352.bindings);
                                               depth = (uu___342_17352.depth);
                                               tcenv = (uu___342_17352.tcenv);
                                               warn = (uu___342_17352.warn);
                                               cache = (uu___342_17352.cache);
                                               nolabels =
                                                 (uu___342_17352.nolabels);
                                               use_zfuel_name =
                                                 (uu___342_17352.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___342_17352.current_module_name)
                                             } in
                                           let uu____17353 =
                                             let uu____17354 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17354 in
                                           if uu____17353
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17346 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17369::uu____17370 ->
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
                                                     let uu____17410 =
                                                       let uu____17421 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17421) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17410 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17448 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17451 =
                                               match formals with
                                               | [] ->
                                                   let uu____17468 =
                                                     let uu____17469 =
                                                       let uu____17472 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17472 in
                                                     push_free_var env1 lid
                                                       vname uu____17469 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17468)
                                               | uu____17477 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17484 =
                                                       let uu____17491 =
                                                         let uu____17492 =
                                                           let uu____17503 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17503) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17492 in
                                                       (uu____17491,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17484 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17451 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17308 with
                                        | (decls2,env2) ->
                                            let uu____17546 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17554 =
                                                encode_term res_t1 env' in
                                              match uu____17554 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17567 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17567, decls) in
                                            (match uu____17546 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17578 =
                                                     let uu____17585 =
                                                       let uu____17586 =
                                                         let uu____17597 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17597) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17586 in
                                                     (uu____17585,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17578 in
                                                 let freshness =
                                                   let uu____17613 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17613
                                                   then
                                                     let uu____17618 =
                                                       let uu____17619 =
                                                         let uu____17630 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17641 =
                                                           varops.next_id () in
                                                         (vname, uu____17630,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17641) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17619 in
                                                     let uu____17644 =
                                                       let uu____17647 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17647] in
                                                     uu____17618 ::
                                                       uu____17644
                                                   else [] in
                                                 let g =
                                                   let uu____17652 =
                                                     let uu____17655 =
                                                       let uu____17658 =
                                                         let uu____17661 =
                                                           let uu____17664 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17664 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17661 in
                                                       FStar_List.append
                                                         decls3 uu____17658 in
                                                     FStar_List.append decls2
                                                       uu____17655 in
                                                   FStar_List.append decls11
                                                     uu____17652 in
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
          let uu____17695 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17695 with
          | FStar_Pervasives_Native.None  ->
              let uu____17732 = encode_free_var false env x t t_norm [] in
              (match uu____17732 with
               | (decls,env1) ->
                   let uu____17759 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17759 with
                    | (n1,x',uu____17786) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17807) ->
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
            let uu____17862 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17862 with
            | (decls,env1) ->
                let uu____17881 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17881
                then
                  let uu____17888 =
                    let uu____17891 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17891 in
                  (uu____17888, env1)
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
             (fun uu____17943  ->
                fun lb  ->
                  match uu____17943 with
                  | (decls,env1) ->
                      let uu____17963 =
                        let uu____17970 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17970
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17963 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____17991 = FStar_Syntax_Util.head_and_args t in
    match uu____17991 with
    | (hd1,args) ->
        let uu____18028 =
          let uu____18029 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18029.FStar_Syntax_Syntax.n in
        (match uu____18028 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18033,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18052 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18074  ->
      fun quals  ->
        match uu____18074 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18150 = FStar_Util.first_N nbinders formals in
              match uu____18150 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18231  ->
                         fun uu____18232  ->
                           match (uu____18231, uu____18232) with
                           | ((formal,uu____18250),(binder,uu____18252)) ->
                               let uu____18261 =
                                 let uu____18268 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18268) in
                               FStar_Syntax_Syntax.NT uu____18261) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18276 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18307  ->
                              match uu____18307 with
                              | (x,i) ->
                                  let uu____18318 =
                                    let uu___343_18319 = x in
                                    let uu____18320 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___343_18319.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___343_18319.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18320
                                    } in
                                  (uu____18318, i))) in
                    FStar_All.pipe_right uu____18276
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18338 =
                      let uu____18339 = FStar_Syntax_Subst.compress body in
                      let uu____18340 =
                        let uu____18341 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18341 in
                      FStar_Syntax_Syntax.extend_app_n uu____18339
                        uu____18340 in
                    uu____18338 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18402 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18402
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___344_18405 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___344_18405.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___344_18405.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___344_18405.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___344_18405.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___344_18405.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___344_18405.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___344_18405.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___344_18405.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___344_18405.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___344_18405.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___344_18405.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___344_18405.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___344_18405.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___344_18405.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___344_18405.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___344_18405.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___344_18405.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___344_18405.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___344_18405.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___344_18405.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___344_18405.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___344_18405.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___344_18405.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___344_18405.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___344_18405.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___344_18405.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___344_18405.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___344_18405.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___344_18405.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___344_18405.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___344_18405.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___344_18405.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___344_18405.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18438 = FStar_Syntax_Util.abs_formals e in
                match uu____18438 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18502::uu____18503 ->
                         let uu____18518 =
                           let uu____18519 =
                             let uu____18522 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18522 in
                           uu____18519.FStar_Syntax_Syntax.n in
                         (match uu____18518 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18565 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18565 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18607 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18607
                                   then
                                     let uu____18642 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18642 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18736  ->
                                                   fun uu____18737  ->
                                                     match (uu____18736,
                                                             uu____18737)
                                                     with
                                                     | ((x,uu____18755),
                                                        (b,uu____18757)) ->
                                                         let uu____18766 =
                                                           let uu____18773 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18773) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18766)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18775 =
                                            let uu____18796 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18796) in
                                          (uu____18775, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18864 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18864 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18953) ->
                              let uu____18958 =
                                let uu____18979 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18979 in
                              (uu____18958, true)
                          | uu____19044 when Prims.op_Negation norm1 ->
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
                          | uu____19046 ->
                              let uu____19047 =
                                let uu____19048 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19049 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19048
                                  uu____19049 in
                              failwith uu____19047)
                     | uu____19074 ->
                         let rec aux' t_norm2 =
                           let uu____19099 =
                             let uu____19100 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19100.FStar_Syntax_Syntax.n in
                           match uu____19099 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19141 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19141 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19169 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19169 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19249)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19254 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19310 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19310
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19322 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19416  ->
                            fun lb  ->
                              match uu____19416 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19511 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19511
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19514 =
                                      let uu____19529 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19529
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19514 with
                                    | (tok,decl,env2) ->
                                        let uu____19575 =
                                          let uu____19588 =
                                            let uu____19599 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19599, tok) in
                                          uu____19588 :: toks in
                                        (uu____19575, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19322 with
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
                        | uu____19782 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19790 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19790 vars)
                            else
                              (let uu____19792 =
                                 let uu____19799 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19799) in
                               FStar_SMTEncoding_Util.mkApp uu____19792) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19881;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19883;
                             FStar_Syntax_Syntax.lbeff = uu____19884;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19947 =
                              let uu____19954 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19954 with
                              | (tcenv',uu____19972,e_t) ->
                                  let uu____19978 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19989 -> failwith "Impossible" in
                                  (match uu____19978 with
                                   | (e1,t_norm1) ->
                                       ((let uu___347_20005 = env2 in
                                         {
                                           bindings =
                                             (uu___347_20005.bindings);
                                           depth = (uu___347_20005.depth);
                                           tcenv = tcenv';
                                           warn = (uu___347_20005.warn);
                                           cache = (uu___347_20005.cache);
                                           nolabels =
                                             (uu___347_20005.nolabels);
                                           use_zfuel_name =
                                             (uu___347_20005.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___347_20005.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___347_20005.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19947 with
                             | (env',e1,t_norm1) ->
                                 let uu____20015 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20015 with
                                  | ((binders,body,uu____20036,uu____20037),curry)
                                      ->
                                      ((let uu____20048 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20048
                                        then
                                          let uu____20049 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20050 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20049 uu____20050
                                        else ());
                                       (let uu____20052 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20052 with
                                        | (vars,guards,env'1,binder_decls,uu____20079)
                                            ->
                                            let body1 =
                                              let uu____20093 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20093
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20096 =
                                              let uu____20105 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20105
                                              then
                                                let uu____20116 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20117 =
                                                  encode_formula body1 env'1 in
                                                (uu____20116, uu____20117)
                                              else
                                                (let uu____20127 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20127)) in
                                            (match uu____20096 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20150 =
                                                     let uu____20157 =
                                                       let uu____20158 =
                                                         let uu____20169 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20169) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20158 in
                                                     let uu____20180 =
                                                       let uu____20183 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20183 in
                                                     (uu____20157,
                                                       uu____20180,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20150 in
                                                 let uu____20186 =
                                                   let uu____20189 =
                                                     let uu____20192 =
                                                       let uu____20195 =
                                                         let uu____20198 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20198 in
                                                       FStar_List.append
                                                         decls2 uu____20195 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20192 in
                                                   FStar_List.append decls1
                                                     uu____20189 in
                                                 (uu____20186, env2))))))
                        | uu____20203 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20288 = varops.fresh "fuel" in
                          (uu____20288, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20291 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20379  ->
                                  fun uu____20380  ->
                                    match (uu____20379, uu____20380) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20528 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20528 in
                                        let gtok =
                                          let uu____20530 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20530 in
                                        let env4 =
                                          let uu____20532 =
                                            let uu____20535 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20535 in
                                          push_free_var env3 flid gtok
                                            uu____20532 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20291 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20691 t_norm
                              uu____20693 =
                              match (uu____20691, uu____20693) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20737;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20738;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20766 =
                                    let uu____20773 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20773 with
                                    | (tcenv',uu____20795,e_t) ->
                                        let uu____20801 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20812 ->
                                              failwith "Impossible" in
                                        (match uu____20801 with
                                         | (e1,t_norm1) ->
                                             ((let uu___348_20828 = env3 in
                                               {
                                                 bindings =
                                                   (uu___348_20828.bindings);
                                                 depth =
                                                   (uu___348_20828.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___348_20828.warn);
                                                 cache =
                                                   (uu___348_20828.cache);
                                                 nolabels =
                                                   (uu___348_20828.nolabels);
                                                 use_zfuel_name =
                                                   (uu___348_20828.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___348_20828.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___348_20828.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20766 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20843 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20843
                                         then
                                           let uu____20844 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20845 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20846 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20844 uu____20845
                                             uu____20846
                                         else ());
                                        (let uu____20848 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20848 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20885 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20885
                                               then
                                                 let uu____20886 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20887 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20888 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20889 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20886 uu____20887
                                                   uu____20888 uu____20889
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20893 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20893 with
                                               | (vars,guards,env'1,binder_decls,uu____20924)
                                                   ->
                                                   let decl_g =
                                                     let uu____20938 =
                                                       let uu____20949 =
                                                         let uu____20952 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20952 in
                                                       (g, uu____20949,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20938 in
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
                                                     let uu____20977 =
                                                       let uu____20984 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20984) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20977 in
                                                   let gsapp =
                                                     let uu____20994 =
                                                       let uu____21001 =
                                                         let uu____21004 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21004 ::
                                                           vars_tm in
                                                       (g, uu____21001) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20994 in
                                                   let gmax =
                                                     let uu____21010 =
                                                       let uu____21017 =
                                                         let uu____21020 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21020 ::
                                                           vars_tm in
                                                       (g, uu____21017) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21010 in
                                                   let body1 =
                                                     let uu____21026 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21026
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21028 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21028 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21046 =
                                                            let uu____21053 =
                                                              let uu____21054
                                                                =
                                                                let uu____21069
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
                                                                  uu____21069) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21054 in
                                                            let uu____21090 =
                                                              let uu____21093
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21093 in
                                                            (uu____21053,
                                                              uu____21090,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21046 in
                                                        let eqn_f =
                                                          let uu____21097 =
                                                            let uu____21104 =
                                                              let uu____21105
                                                                =
                                                                let uu____21116
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21116) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21105 in
                                                            (uu____21104,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21097 in
                                                        let eqn_g' =
                                                          let uu____21130 =
                                                            let uu____21137 =
                                                              let uu____21138
                                                                =
                                                                let uu____21149
                                                                  =
                                                                  let uu____21150
                                                                    =
                                                                    let uu____21155
                                                                    =
                                                                    let uu____21156
                                                                    =
                                                                    let uu____21163
                                                                    =
                                                                    let uu____21166
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21166
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21163) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21156 in
                                                                    (gsapp,
                                                                    uu____21155) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21150 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21149) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21138 in
                                                            (uu____21137,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21130 in
                                                        let uu____21189 =
                                                          let uu____21198 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21198
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21227)
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
                                                                  let uu____21252
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21252
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21257
                                                                  =
                                                                  let uu____21264
                                                                    =
                                                                    let uu____21265
                                                                    =
                                                                    let uu____21276
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21276) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21265 in
                                                                  (uu____21264,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21257 in
                                                              let uu____21297
                                                                =
                                                                let uu____21304
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21304
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21317
                                                                    =
                                                                    let uu____21320
                                                                    =
                                                                    let uu____21321
                                                                    =
                                                                    let uu____21328
                                                                    =
                                                                    let uu____21329
                                                                    =
                                                                    let uu____21340
                                                                    =
                                                                    let uu____21341
                                                                    =
                                                                    let uu____21346
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21346,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21341 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21340) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21329 in
                                                                    (uu____21328,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21321 in
                                                                    [uu____21320] in
                                                                    (d3,
                                                                    uu____21317) in
                                                              (match uu____21297
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21189
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
                            let uu____21411 =
                              let uu____21424 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21503  ->
                                   fun uu____21504  ->
                                     match (uu____21503, uu____21504) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21659 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21659 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21424 in
                            (match uu____21411 with
                             | (decls2,eqns,env01) ->
                                 let uu____21732 =
                                   let isDeclFun uu___314_21744 =
                                     match uu___314_21744 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21745 -> true
                                     | uu____21756 -> false in
                                   let uu____21757 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21757
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21732 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21797 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___315_21801  ->
                                 match uu___315_21801 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21802 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21808 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21808))) in
                      if uu____21797
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
                   let uu____21860 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21860
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
        let uu____21909 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21909 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21913 = encode_sigelt' env se in
      match uu____21913 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21929 =
                  let uu____21930 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21930 in
                [uu____21929]
            | uu____21931 ->
                let uu____21932 =
                  let uu____21935 =
                    let uu____21936 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21936 in
                  uu____21935 :: g in
                let uu____21937 =
                  let uu____21940 =
                    let uu____21941 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21941 in
                  [uu____21940] in
                FStar_List.append uu____21932 uu____21937 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21954 =
          let uu____21955 = FStar_Syntax_Subst.compress t in
          uu____21955.FStar_Syntax_Syntax.n in
        match uu____21954 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21959)) -> s = "opaque_to_smt"
        | uu____21960 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21965 =
          let uu____21966 = FStar_Syntax_Subst.compress t in
          uu____21966.FStar_Syntax_Syntax.n in
        match uu____21965 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21970)) -> s = "uninterpreted_by_smt"
        | uu____21971 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21976 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21981 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21984 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21987 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22002 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22006 =
            let uu____22007 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22007 Prims.op_Negation in
          if uu____22006
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22033 ->
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
               let uu____22053 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22053 with
               | (aname,atok,env2) ->
                   let uu____22069 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22069 with
                    | (formals,uu____22087) ->
                        let uu____22100 =
                          let uu____22105 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22105 env2 in
                        (match uu____22100 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22117 =
                                 let uu____22118 =
                                   let uu____22129 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22145  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22129,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22118 in
                               [uu____22117;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22158 =
                               let aux uu____22210 uu____22211 =
                                 match (uu____22210, uu____22211) with
                                 | ((bv,uu____22263),(env3,acc_sorts,acc)) ->
                                     let uu____22301 = gen_term_var env3 bv in
                                     (match uu____22301 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22158 with
                              | (uu____22373,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22396 =
                                      let uu____22403 =
                                        let uu____22404 =
                                          let uu____22415 =
                                            let uu____22416 =
                                              let uu____22421 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22421) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22416 in
                                          ([[app]], xs_sorts, uu____22415) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22404 in
                                      (uu____22403,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22396 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22441 =
                                      let uu____22448 =
                                        let uu____22449 =
                                          let uu____22460 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22460) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22449 in
                                      (uu____22448,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22441 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22479 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22479 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22507,uu____22508)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22509 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22509 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22526,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22532 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___316_22536  ->
                      match uu___316_22536 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22537 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22542 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22543 -> false)) in
            Prims.op_Negation uu____22532 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22552 =
               let uu____22559 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22559 env fv t quals in
             match uu____22552 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22574 =
                   let uu____22577 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22577 in
                 (uu____22574, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22585 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22585 with
           | (uu____22594,f1) ->
               let uu____22596 = encode_formula f1 env in
               (match uu____22596 with
                | (f2,decls) ->
                    let g =
                      let uu____22610 =
                        let uu____22611 =
                          let uu____22618 =
                            let uu____22621 =
                              let uu____22622 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22622 in
                            FStar_Pervasives_Native.Some uu____22621 in
                          let uu____22623 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22618, uu____22623) in
                        FStar_SMTEncoding_Util.mkAssume uu____22611 in
                      [uu____22610] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22629) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22641 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22659 =
                       let uu____22662 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22662.FStar_Syntax_Syntax.fv_name in
                     uu____22659.FStar_Syntax_Syntax.v in
                   let uu____22663 =
                     let uu____22664 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22664 in
                   if uu____22663
                   then
                     let val_decl =
                       let uu___351_22692 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___351_22692.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___351_22692.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___351_22692.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22697 = encode_sigelt' env1 val_decl in
                     match uu____22697 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22641 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22725,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22727;
                          FStar_Syntax_Syntax.lbtyp = uu____22728;
                          FStar_Syntax_Syntax.lbeff = uu____22729;
                          FStar_Syntax_Syntax.lbdef = uu____22730;_}::[]),uu____22731)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22750 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22750 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22779 =
                   let uu____22782 =
                     let uu____22783 =
                       let uu____22790 =
                         let uu____22791 =
                           let uu____22802 =
                             let uu____22803 =
                               let uu____22808 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22808) in
                             FStar_SMTEncoding_Util.mkEq uu____22803 in
                           ([[b2t_x]], [xx], uu____22802) in
                         FStar_SMTEncoding_Util.mkForall uu____22791 in
                       (uu____22790,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22783 in
                   [uu____22782] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22779 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22841,uu____22842) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___317_22851  ->
                  match uu___317_22851 with
                  | FStar_Syntax_Syntax.Discriminator uu____22852 -> true
                  | uu____22853 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22856,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22867 =
                     let uu____22868 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22868.FStar_Ident.idText in
                   uu____22867 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___318_22872  ->
                     match uu___318_22872 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22873 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22877) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___319_22894  ->
                  match uu___319_22894 with
                  | FStar_Syntax_Syntax.Projector uu____22895 -> true
                  | uu____22900 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22903 = try_lookup_free_var env l in
          (match uu____22903 with
           | FStar_Pervasives_Native.Some uu____22910 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___352_22914 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___352_22914.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___352_22914.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___352_22914.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22921) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22939) ->
          let uu____22948 = encode_sigelts env ses in
          (match uu____22948 with
           | (g,env1) ->
               let uu____22965 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___320_22988  ->
                         match uu___320_22988 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22989;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22990;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22991;_}
                             -> false
                         | uu____22994 -> true)) in
               (match uu____22965 with
                | (g',inversions) ->
                    let uu____23009 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___321_23030  ->
                              match uu___321_23030 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23031 ->
                                  true
                              | uu____23042 -> false)) in
                    (match uu____23009 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23060,tps,k,uu____23063,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___322_23080  ->
                    match uu___322_23080 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23081 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23090 = c in
              match uu____23090 with
              | (name,args,uu____23095,uu____23096,uu____23097) ->
                  let uu____23102 =
                    let uu____23103 =
                      let uu____23114 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23131  ->
                                match uu____23131 with
                                | (uu____23138,sort,uu____23140) -> sort)) in
                      (name, uu____23114, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23103 in
                  [uu____23102]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23167 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23173 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23173 FStar_Option.isNone)) in
            if uu____23167
            then []
            else
              (let uu____23205 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23205 with
               | (xxsym,xx) ->
                   let uu____23214 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23253  ->
                             fun l  ->
                               match uu____23253 with
                               | (out,decls) ->
                                   let uu____23273 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23273 with
                                    | (uu____23284,data_t) ->
                                        let uu____23286 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23286 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23332 =
                                                 let uu____23333 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23333.FStar_Syntax_Syntax.n in
                                               match uu____23332 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23344,indices) ->
                                                   indices
                                               | uu____23366 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23390  ->
                                                         match uu____23390
                                                         with
                                                         | (x,uu____23396) ->
                                                             let uu____23397
                                                               =
                                                               let uu____23398
                                                                 =
                                                                 let uu____23405
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23405,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23398 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23397)
                                                    env) in
                                             let uu____23408 =
                                               encode_args indices env1 in
                                             (match uu____23408 with
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
                                                      let uu____23434 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23450
                                                                 =
                                                                 let uu____23455
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23455,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23450)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23434
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23458 =
                                                      let uu____23459 =
                                                        let uu____23464 =
                                                          let uu____23465 =
                                                            let uu____23470 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23470,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23465 in
                                                        (out, uu____23464) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23459 in
                                                    (uu____23458,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23214 with
                    | (data_ax,decls) ->
                        let uu____23483 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23483 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23494 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23494 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23498 =
                                 let uu____23505 =
                                   let uu____23506 =
                                     let uu____23517 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23532 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23517,
                                       uu____23532) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23506 in
                                 let uu____23547 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23505,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23547) in
                               FStar_SMTEncoding_Util.mkAssume uu____23498 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23550 =
            let uu____23563 =
              let uu____23564 = FStar_Syntax_Subst.compress k in
              uu____23564.FStar_Syntax_Syntax.n in
            match uu____23563 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23609 -> (tps, k) in
          (match uu____23550 with
           | (formals,res) ->
               let uu____23632 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23632 with
                | (formals1,res1) ->
                    let uu____23643 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23643 with
                     | (vars,guards,env',binder_decls,uu____23668) ->
                         let uu____23681 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23681 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23700 =
                                  let uu____23707 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23707) in
                                FStar_SMTEncoding_Util.mkApp uu____23700 in
                              let uu____23716 =
                                let tname_decl =
                                  let uu____23726 =
                                    let uu____23727 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23759  ->
                                              match uu____23759 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23772 = varops.next_id () in
                                    (tname, uu____23727,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23772, false) in
                                  constructor_or_logic_type_decl uu____23726 in
                                let uu____23781 =
                                  match vars with
                                  | [] ->
                                      let uu____23794 =
                                        let uu____23795 =
                                          let uu____23798 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23798 in
                                        push_free_var env1 t tname
                                          uu____23795 in
                                      ([], uu____23794)
                                  | uu____23805 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23814 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23814 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23828 =
                                          let uu____23835 =
                                            let uu____23836 =
                                              let uu____23851 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23851) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23836 in
                                          (uu____23835,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23828 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23781 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23716 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23891 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23891 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23909 =
                                               let uu____23910 =
                                                 let uu____23917 =
                                                   let uu____23918 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23918 in
                                                 (uu____23917,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23910 in
                                             [uu____23909]
                                           else [] in
                                         let uu____23922 =
                                           let uu____23925 =
                                             let uu____23928 =
                                               let uu____23929 =
                                                 let uu____23936 =
                                                   let uu____23937 =
                                                     let uu____23948 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23948) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23937 in
                                                 (uu____23936,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23929 in
                                             [uu____23928] in
                                           FStar_List.append karr uu____23925 in
                                         FStar_List.append decls1 uu____23922 in
                                   let aux =
                                     let uu____23964 =
                                       let uu____23967 =
                                         inversion_axioms tapp vars in
                                       let uu____23970 =
                                         let uu____23973 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23973] in
                                       FStar_List.append uu____23967
                                         uu____23970 in
                                     FStar_List.append kindingAx uu____23964 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23980,uu____23981,uu____23982,uu____23983,uu____23984)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23992,t,uu____23994,n_tps,uu____23996) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24004 = new_term_constant_and_tok_from_lid env d in
          (match uu____24004 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24021 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24021 with
                | (formals,t_res) ->
                    let uu____24056 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24056 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24070 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24070 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24140 =
                                            mk_term_projector_name d x in
                                          (uu____24140,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24142 =
                                  let uu____24161 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24161, true) in
                                FStar_All.pipe_right uu____24142
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
                              let uu____24200 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24200 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24212::uu____24213 ->
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
                                         let uu____24258 =
                                           let uu____24269 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24269) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24258
                                     | uu____24294 -> tok_typing in
                                   let uu____24303 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24303 with
                                    | (vars',guards',env'',decls_formals,uu____24328)
                                        ->
                                        let uu____24341 =
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
                                        (match uu____24341 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24372 ->
                                                   let uu____24379 =
                                                     let uu____24380 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24380 in
                                                   [uu____24379] in
                                             let encode_elim uu____24390 =
                                               let uu____24391 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24391 with
                                               | (head1,args) ->
                                                   let uu____24434 =
                                                     let uu____24435 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24435.FStar_Syntax_Syntax.n in
                                                   (match uu____24434 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24445;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24446;_},uu____24447)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24453 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24453
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
                                                                 | uu____24496
                                                                    ->
                                                                    let uu____24497
                                                                    =
                                                                    let uu____24498
                                                                    =
                                                                    let uu____24503
                                                                    =
                                                                    let uu____24504
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24504 in
                                                                    (uu____24503,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24498 in
                                                                    FStar_Exn.raise
                                                                    uu____24497 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24520
                                                                    =
                                                                    let uu____24521
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24521 in
                                                                    if
                                                                    uu____24520
                                                                    then
                                                                    let uu____24534
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24534]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24536
                                                               =
                                                               let uu____24549
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24599
                                                                     ->
                                                                    fun
                                                                    uu____24600
                                                                     ->
                                                                    match 
                                                                    (uu____24599,
                                                                    uu____24600)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24695
                                                                    =
                                                                    let uu____24702
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24702 in
                                                                    (match uu____24695
                                                                    with
                                                                    | 
                                                                    (uu____24715,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24723
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24723
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24725
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24725
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
                                                                 uu____24549 in
                                                             (match uu____24536
                                                              with
                                                              | (uu____24740,arg_vars,elim_eqns_or_guards,uu____24743)
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
                                                                    let uu____24773
                                                                    =
                                                                    let uu____24780
                                                                    =
                                                                    let uu____24781
                                                                    =
                                                                    let uu____24792
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24803
                                                                    =
                                                                    let uu____24804
                                                                    =
                                                                    let uu____24809
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24809) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24804 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24792,
                                                                    uu____24803) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24781 in
                                                                    (uu____24780,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24773 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24832
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24832,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24834
                                                                    =
                                                                    let uu____24841
                                                                    =
                                                                    let uu____24842
                                                                    =
                                                                    let uu____24853
                                                                    =
                                                                    let uu____24858
                                                                    =
                                                                    let uu____24861
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24861] in
                                                                    [uu____24858] in
                                                                    let uu____24866
                                                                    =
                                                                    let uu____24867
                                                                    =
                                                                    let uu____24872
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24873
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24872,
                                                                    uu____24873) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24867 in
                                                                    (uu____24853,
                                                                    [x],
                                                                    uu____24866) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24842 in
                                                                    let uu____24892
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24841,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24892) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24834
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24899
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
                                                                    (let uu____24927
                                                                    =
                                                                    let uu____24928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24928
                                                                    dapp1 in
                                                                    [uu____24927]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24899
                                                                    FStar_List.flatten in
                                                                    let uu____24935
                                                                    =
                                                                    let uu____24942
                                                                    =
                                                                    let uu____24943
                                                                    =
                                                                    let uu____24954
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24965
                                                                    =
                                                                    let uu____24966
                                                                    =
                                                                    let uu____24971
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24971) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24966 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24954,
                                                                    uu____24965) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24943 in
                                                                    (uu____24942,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24935) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24992 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24992
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
                                                                 | uu____25035
                                                                    ->
                                                                    let uu____25036
                                                                    =
                                                                    let uu____25037
                                                                    =
                                                                    let uu____25042
                                                                    =
                                                                    let uu____25043
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25043 in
                                                                    (uu____25042,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25037 in
                                                                    FStar_Exn.raise
                                                                    uu____25036 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25059
                                                                    =
                                                                    let uu____25060
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25060 in
                                                                    if
                                                                    uu____25059
                                                                    then
                                                                    let uu____25073
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25073]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25075
                                                               =
                                                               let uu____25088
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25138
                                                                     ->
                                                                    fun
                                                                    uu____25139
                                                                     ->
                                                                    match 
                                                                    (uu____25138,
                                                                    uu____25139)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25234
                                                                    =
                                                                    let uu____25241
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25241 in
                                                                    (match uu____25234
                                                                    with
                                                                    | 
                                                                    (uu____25254,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25262
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25262
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25264
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25264
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
                                                                 uu____25088 in
                                                             (match uu____25075
                                                              with
                                                              | (uu____25279,arg_vars,elim_eqns_or_guards,uu____25282)
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
                                                                    let uu____25312
                                                                    =
                                                                    let uu____25319
                                                                    =
                                                                    let uu____25320
                                                                    =
                                                                    let uu____25331
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25342
                                                                    =
                                                                    let uu____25343
                                                                    =
                                                                    let uu____25348
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25348) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25343 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25331,
                                                                    uu____25342) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25320 in
                                                                    (uu____25319,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25312 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25371
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25371,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25373
                                                                    =
                                                                    let uu____25380
                                                                    =
                                                                    let uu____25381
                                                                    =
                                                                    let uu____25392
                                                                    =
                                                                    let uu____25397
                                                                    =
                                                                    let uu____25400
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25400] in
                                                                    [uu____25397] in
                                                                    let uu____25405
                                                                    =
                                                                    let uu____25406
                                                                    =
                                                                    let uu____25411
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25412
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25411,
                                                                    uu____25412) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25406 in
                                                                    (uu____25392,
                                                                    [x],
                                                                    uu____25405) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25381 in
                                                                    let uu____25431
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25380,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25431) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25373
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25438
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
                                                                    (let uu____25466
                                                                    =
                                                                    let uu____25467
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25467
                                                                    dapp1 in
                                                                    [uu____25466]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25438
                                                                    FStar_List.flatten in
                                                                    let uu____25474
                                                                    =
                                                                    let uu____25481
                                                                    =
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25493
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25504
                                                                    =
                                                                    let uu____25505
                                                                    =
                                                                    let uu____25510
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25510) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25505 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25493,
                                                                    uu____25504) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25482 in
                                                                    (uu____25481,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25474) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25529 ->
                                                        ((let uu____25531 =
                                                            let uu____25532 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25533 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25532
                                                              uu____25533 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25531);
                                                         ([], []))) in
                                             let uu____25538 = encode_elim () in
                                             (match uu____25538 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25558 =
                                                      let uu____25561 =
                                                        let uu____25564 =
                                                          let uu____25567 =
                                                            let uu____25570 =
                                                              let uu____25571
                                                                =
                                                                let uu____25582
                                                                  =
                                                                  let uu____25585
                                                                    =
                                                                    let uu____25586
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25586 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25585 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25582) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25571 in
                                                            [uu____25570] in
                                                          let uu____25591 =
                                                            let uu____25594 =
                                                              let uu____25597
                                                                =
                                                                let uu____25600
                                                                  =
                                                                  let uu____25603
                                                                    =
                                                                    let uu____25606
                                                                    =
                                                                    let uu____25609
                                                                    =
                                                                    let uu____25610
                                                                    =
                                                                    let uu____25617
                                                                    =
                                                                    let uu____25618
                                                                    =
                                                                    let uu____25629
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25629) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25618 in
                                                                    (uu____25617,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25610 in
                                                                    let uu____25642
                                                                    =
                                                                    let uu____25645
                                                                    =
                                                                    let uu____25646
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25665,
                                                                    uu____25676) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25654 in
                                                                    (uu____25653,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25646 in
                                                                    [uu____25645] in
                                                                    uu____25609
                                                                    ::
                                                                    uu____25642 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25606 in
                                                                  FStar_List.append
                                                                    uu____25603
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25600 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25597 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25594 in
                                                          FStar_List.append
                                                            uu____25567
                                                            uu____25591 in
                                                        FStar_List.append
                                                          decls3 uu____25564 in
                                                      FStar_List.append
                                                        decls2 uu____25561 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25558 in
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
           (fun uu____25722  ->
              fun se  ->
                match uu____25722 with
                | (g,env1) ->
                    let uu____25742 = encode_sigelt env1 se in
                    (match uu____25742 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25799 =
        match uu____25799 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25831 ->
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
                 ((let uu____25837 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25837
                   then
                     let uu____25838 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25839 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25840 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25838 uu____25839 uu____25840
                   else ());
                  (let uu____25842 = encode_term t1 env1 in
                   match uu____25842 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25858 =
                         let uu____25865 =
                           let uu____25866 =
                             let uu____25867 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25867
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25866 in
                         new_term_constant_from_string env1 x uu____25865 in
                       (match uu____25858 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25883 = FStar_Options.log_queries () in
                              if uu____25883
                              then
                                let uu____25886 =
                                  let uu____25887 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25888 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25889 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25887 uu____25888 uu____25889 in
                                FStar_Pervasives_Native.Some uu____25886
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25905,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25919 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25919 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25942,se,uu____25944) ->
                 let uu____25949 = encode_sigelt env1 se in
                 (match uu____25949 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25966,se) ->
                 let uu____25972 = encode_sigelt env1 se in
                 (match uu____25972 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25989 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25989 with | (uu____26012,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26024 'Auu____26025 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26025,'Auu____26024)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26093  ->
              match uu____26093 with
              | (l,uu____26105,uu____26106) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26152  ->
              match uu____26152 with
              | (l,uu____26166,uu____26167) ->
                  let uu____26176 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26177 =
                    let uu____26180 =
                      let uu____26181 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26181 in
                    [uu____26180] in
                  uu____26176 :: uu____26177)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26202 =
      let uu____26205 =
        let uu____26206 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26209 =
          let uu____26210 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26210 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26206;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26209
        } in
      [uu____26205] in
    FStar_ST.op_Colon_Equals last_env uu____26202
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26267 = FStar_ST.op_Bang last_env in
      match uu____26267 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26321 ->
          let uu___353_26324 = e in
          let uu____26325 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___353_26324.bindings);
            depth = (uu___353_26324.depth);
            tcenv;
            warn = (uu___353_26324.warn);
            cache = (uu___353_26324.cache);
            nolabels = (uu___353_26324.nolabels);
            use_zfuel_name = (uu___353_26324.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___353_26324.encode_non_total_function_typ);
            current_module_name = uu____26325
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26329 = FStar_ST.op_Bang last_env in
    match uu____26329 with
    | [] -> failwith "Empty env stack"
    | uu____26382::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26438  ->
    let uu____26439 = FStar_ST.op_Bang last_env in
    match uu____26439 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___354_26500 = hd1 in
          {
            bindings = (uu___354_26500.bindings);
            depth = (uu___354_26500.depth);
            tcenv = (uu___354_26500.tcenv);
            warn = (uu___354_26500.warn);
            cache = refs;
            nolabels = (uu___354_26500.nolabels);
            use_zfuel_name = (uu___354_26500.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___354_26500.encode_non_total_function_typ);
            current_module_name = (uu___354_26500.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26553  ->
    let uu____26554 = FStar_ST.op_Bang last_env in
    match uu____26554 with
    | [] -> failwith "Popping an empty stack"
    | uu____26607::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26698::uu____26699,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___355_26707 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___355_26707.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___355_26707.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___355_26707.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26708 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26723 =
        let uu____26726 =
          let uu____26727 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26727 in
        let uu____26728 = open_fact_db_tags env in uu____26726 :: uu____26728 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26723
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
      let uu____26750 = encode_sigelt env se in
      match uu____26750 with
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
        let uu____26786 = FStar_Options.log_queries () in
        if uu____26786
        then
          let uu____26789 =
            let uu____26790 =
              let uu____26791 =
                let uu____26792 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26792 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26791 in
            FStar_SMTEncoding_Term.Caption uu____26790 in
          uu____26789 :: decls
        else decls in
      (let uu____26803 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26803
       then
         let uu____26804 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26804
       else ());
      (let env =
         let uu____26807 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26807 tcenv in
       let uu____26808 = encode_top_level_facts env se in
       match uu____26808 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26822 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26822)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26834 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26834
       then
         let uu____26835 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26835
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26870  ->
                 fun se  ->
                   match uu____26870 with
                   | (g,env2) ->
                       let uu____26890 = encode_top_level_facts env2 se in
                       (match uu____26890 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26913 =
         encode_signature
           (let uu___356_26922 = env in
            {
              bindings = (uu___356_26922.bindings);
              depth = (uu___356_26922.depth);
              tcenv = (uu___356_26922.tcenv);
              warn = false;
              cache = (uu___356_26922.cache);
              nolabels = (uu___356_26922.nolabels);
              use_zfuel_name = (uu___356_26922.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___356_26922.encode_non_total_function_typ);
              current_module_name = (uu___356_26922.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26913 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26939 = FStar_Options.log_queries () in
             if uu____26939
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___357_26947 = env1 in
               {
                 bindings = (uu___357_26947.bindings);
                 depth = (uu___357_26947.depth);
                 tcenv = (uu___357_26947.tcenv);
                 warn = true;
                 cache = (uu___357_26947.cache);
                 nolabels = (uu___357_26947.nolabels);
                 use_zfuel_name = (uu___357_26947.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___357_26947.encode_non_total_function_typ);
                 current_module_name = (uu___357_26947.current_module_name)
               });
            (let uu____26949 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26949
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
        (let uu____27001 =
           let uu____27002 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27002.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27001);
        (let env =
           let uu____27004 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27004 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27016 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27051 = aux rest in
                 (match uu____27051 with
                  | (out,rest1) ->
                      let t =
                        let uu____27081 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27081 with
                        | FStar_Pervasives_Native.Some uu____27086 ->
                            let uu____27087 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27087
                              x.FStar_Syntax_Syntax.sort
                        | uu____27088 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27092 =
                        let uu____27095 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___358_27098 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___358_27098.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___358_27098.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27095 :: out in
                      (uu____27092, rest1))
             | uu____27103 -> ([], bindings1) in
           let uu____27110 = aux bindings in
           match uu____27110 with
           | (closing,bindings1) ->
               let uu____27135 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27135, bindings1) in
         match uu____27016 with
         | (q1,bindings1) ->
             let uu____27158 =
               let uu____27163 =
                 FStar_List.filter
                   (fun uu___323_27168  ->
                      match uu___323_27168 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27169 ->
                          false
                      | uu____27176 -> true) bindings1 in
               encode_env_bindings env uu____27163 in
             (match uu____27158 with
              | (env_decls,env1) ->
                  ((let uu____27194 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27194
                    then
                      let uu____27195 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27195
                    else ());
                   (let uu____27197 = encode_formula q1 env1 in
                    match uu____27197 with
                    | (phi,qdecls) ->
                        let uu____27218 =
                          let uu____27223 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27223 phi in
                        (match uu____27218 with
                         | (labels,phi1) ->
                             let uu____27240 = encode_labels labels in
                             (match uu____27240 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27277 =
                                      let uu____27284 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27285 =
                                        varops.mk_unique "@query" in
                                      (uu____27284,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27285) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27277 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))