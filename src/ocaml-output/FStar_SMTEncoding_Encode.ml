open Prims
let add_fuel:
  'Auu____7 . 'Auu____7 -> 'Auu____7 Prims.list -> 'Auu____7 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____22 = FStar_Options.unthrottle_inductives () in
      if uu____22 then tl1 else x :: tl1
let withenv:
  'Auu____36 'Auu____37 'Auu____38 .
    'Auu____38 ->
      ('Auu____37,'Auu____36) FStar_Pervasives_Native.tuple2 ->
        ('Auu____37,'Auu____36,'Auu____38) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____56  -> match uu____56 with | (a,b) -> (a, b, c)
let vargs:
  'Auu____71 'Auu____72 'Auu____73 .
    (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___108_119  ->
         match uu___108_119 with
         | (FStar_Util.Inl uu____128,uu____129) -> false
         | uu____134 -> true) args
let subst_lcomp_opt:
  'Auu____149 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____185 =
            let uu____190 =
              let uu____191 =
                let uu____194 = l1.FStar_Syntax_Syntax.comp () in
                FStar_Syntax_Subst.subst_comp s uu____194 in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191 in
            FStar_Util.Inl uu____190 in
          FStar_Pervasives_Native.Some uu____185
      | uu____201 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___132_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___132_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___132_221.FStar_Syntax_Syntax.sort)
        } in
      let uu____223 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____223
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____239 =
          let uu____240 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____240 in
        let uu____241 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____241 with
        | (uu____246,t) ->
            let uu____248 =
              let uu____249 = FStar_Syntax_Subst.compress t in
              uu____249.FStar_Syntax_Syntax.n in
            (match uu____248 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____270 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____270 with
                  | (binders,uu____276) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____291 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____300 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____300
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____309 =
        let uu____314 = mk_term_projector_name lid a in
        (uu____314,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____309
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____323 =
        let uu____328 = mk_term_projector_name_by_pos lid i in
        (uu____328,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____323
let mk_data_tester:
  'Auu____337 .
    'Auu____337 ->
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
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}[@@deriving show]
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
let __proj__Mkvarops_t__item__mark: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mark
let __proj__Mkvarops_t__item__reset_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__reset_mark
let __proj__Mkvarops_t__item__commit_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__commit_mark
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____946 =
    let uu____947 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____950 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____947, uu____950) in
  let scopes =
    let uu____970 = let uu____981 = new_scope () in [uu____981] in
    FStar_Util.mk_ref uu____970 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____1022 =
        let uu____1025 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____1025
          (fun uu____1111  ->
             match uu____1111 with
             | (names1,uu____1123) -> FStar_Util.smap_try_find names1 y1) in
      match uu____1022 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1132 ->
          (FStar_Util.incr ctr;
           (let uu____1155 =
              let uu____1156 =
                let uu____1157 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____1157 in
              Prims.strcat "__" uu____1156 in
            Prims.strcat y1 uu____1155)) in
    let top_scope =
      let uu____1185 =
        let uu____1194 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1194 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1185 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1306 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1357 =
      let uu____1358 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1358 in
    FStar_Util.format2 "%s_%s" pfx uu____1357 in
  let string_const s =
    let uu____1363 =
      let uu____1366 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1366
        (fun uu____1452  ->
           match uu____1452 with
           | (uu____1463,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1363 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 () in
        let f =
          let uu____1476 = FStar_SMTEncoding_Util.mk_String_const id1 in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1476 in
        let top_scope =
          let uu____1480 =
            let uu____1489 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1489 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1480 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1590 =
    let uu____1591 =
      let uu____1602 = new_scope () in
      let uu____1611 = FStar_ST.op_Bang scopes in uu____1602 :: uu____1611 in
    FStar_ST.op_Colon_Equals scopes uu____1591 in
  let pop1 uu____1761 =
    let uu____1762 =
      let uu____1773 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1773 in
    FStar_ST.op_Colon_Equals scopes uu____1762 in
  let mark1 uu____1923 = push1 () in
  let reset_mark1 uu____1927 = pop1 () in
  let commit_mark1 uu____1931 =
    let uu____1932 = FStar_ST.op_Bang scopes in
    match uu____1932 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.op_Colon_Equals scopes ((next1, next2) :: tl1))
    | uu____2144 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___133_2159 = x in
    let uu____2160 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____2160;
      FStar_Syntax_Syntax.index = (uu___133_2159.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___133_2159.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____2194 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____2232 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____2283 'Auu____2284 .
    'Auu____2284 ->
      ('Auu____2284,'Auu____2283 FStar_Pervasives_Native.option)
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
  'Auu____2598 .
    'Auu____2598 ->
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
                 (fun uu___109_2632  ->
                    match uu___109_2632 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2636 -> [])) in
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
    let uu____2647 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___110_2657  ->
              match uu___110_2657 with
              | Binding_var (x,uu____2659) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2661,uu____2662,uu____2663) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2647 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2680 .
    env_t ->
      (binding -> 'Auu____2680 FStar_Pervasives_Native.option) ->
        'Auu____2680 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2710 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2710
      then
        let uu____2713 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2713
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
      let uu____2728 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2728)
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
        (let uu___134_2746 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___134_2746.tcenv);
           warn = (uu___134_2746.warn);
           cache = (uu___134_2746.cache);
           nolabels = (uu___134_2746.nolabels);
           use_zfuel_name = (uu___134_2746.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___134_2746.encode_non_total_function_typ);
           current_module_name = (uu___134_2746.current_module_name)
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
        (let uu___135_2766 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___135_2766.depth);
           tcenv = (uu___135_2766.tcenv);
           warn = (uu___135_2766.warn);
           cache = (uu___135_2766.cache);
           nolabels = (uu___135_2766.nolabels);
           use_zfuel_name = (uu___135_2766.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___135_2766.encode_non_total_function_typ);
           current_module_name = (uu___135_2766.current_module_name)
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
          (let uu___136_2790 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___136_2790.depth);
             tcenv = (uu___136_2790.tcenv);
             warn = (uu___136_2790.warn);
             cache = (uu___136_2790.cache);
             nolabels = (uu___136_2790.nolabels);
             use_zfuel_name = (uu___136_2790.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___136_2790.encode_non_total_function_typ);
             current_module_name = (uu___136_2790.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___137_2803 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___137_2803.depth);
          tcenv = (uu___137_2803.tcenv);
          warn = (uu___137_2803.warn);
          cache = (uu___137_2803.cache);
          nolabels = (uu___137_2803.nolabels);
          use_zfuel_name = (uu___137_2803.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___137_2803.encode_non_total_function_typ);
          current_module_name = (uu___137_2803.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___111_2829  ->
             match uu___111_2829 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2842 -> FStar_Pervasives_Native.None) in
      let uu____2847 = aux a in
      match uu____2847 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2859 = aux a2 in
          (match uu____2859 with
           | FStar_Pervasives_Native.None  ->
               let uu____2870 =
                 let uu____2871 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2872 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2871 uu____2872 in
               failwith uu____2870
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
      let uu____2901 =
        let uu___138_2902 = env in
        let uu____2903 =
          let uu____2906 =
            let uu____2907 =
              let uu____2920 =
                let uu____2923 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2923 in
              (x, fname, uu____2920, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2907 in
          uu____2906 :: (env.bindings) in
        {
          bindings = uu____2903;
          depth = (uu___138_2902.depth);
          tcenv = (uu___138_2902.tcenv);
          warn = (uu___138_2902.warn);
          cache = (uu___138_2902.cache);
          nolabels = (uu___138_2902.nolabels);
          use_zfuel_name = (uu___138_2902.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___138_2902.encode_non_total_function_typ);
          current_module_name = (uu___138_2902.current_module_name)
        } in
      (fname, ftok, uu____2901)
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
        (fun uu___112_2967  ->
           match uu___112_2967 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____3006 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____3025 =
        lookup_binding env
          (fun uu___113_3033  ->
             match uu___113_3033 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____3048 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____3025 FStar_Option.isSome
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
      let uu____3069 = try_lookup_lid env a in
      match uu____3069 with
      | FStar_Pervasives_Native.None  ->
          let uu____3102 =
            let uu____3103 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____3103 in
          failwith uu____3102
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
          let uu___139_3155 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___139_3155.depth);
            tcenv = (uu___139_3155.tcenv);
            warn = (uu___139_3155.warn);
            cache = (uu___139_3155.cache);
            nolabels = (uu___139_3155.nolabels);
            use_zfuel_name = (uu___139_3155.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___139_3155.encode_non_total_function_typ);
            current_module_name = (uu___139_3155.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____3172 = lookup_lid env x in
        match uu____3172 with
        | (t1,t2,uu____3185) ->
            let t3 =
              let uu____3195 =
                let uu____3202 =
                  let uu____3205 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____3205] in
                (f, uu____3202) in
              FStar_SMTEncoding_Util.mkApp uu____3195 in
            let uu___140_3210 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___140_3210.depth);
              tcenv = (uu___140_3210.tcenv);
              warn = (uu___140_3210.warn);
              cache = (uu___140_3210.cache);
              nolabels = (uu___140_3210.nolabels);
              use_zfuel_name = (uu___140_3210.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___140_3210.encode_non_total_function_typ);
              current_module_name = (uu___140_3210.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3225 = try_lookup_lid env l in
      match uu____3225 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3274 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3282,fuel::[]) ->
                         let uu____3286 =
                           let uu____3287 =
                             let uu____3288 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____3288
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____3287 "fuel" in
                         if uu____3286
                         then
                           let uu____3291 =
                             let uu____3292 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3292
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____3291
                         else FStar_Pervasives_Native.Some t
                     | uu____3296 -> FStar_Pervasives_Native.Some t)
                | uu____3297 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3312 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3312 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3316 =
            let uu____3317 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3317 in
          failwith uu____3316
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3330 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3330 with | (x,uu____3342,uu____3343) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3370 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3370 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3406;
                 FStar_SMTEncoding_Term.rng = uu____3407;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3422 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3446 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_3464  ->
           match uu___114_3464 with
           | Binding_fvar (uu____3467,nm',tok,uu____3470) when nm = nm' ->
               tok
           | uu____3479 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3486 .
    'Auu____3486 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3504  ->
      match uu____3504 with
      | (pats,vars,body) ->
          let fallback uu____3529 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3534 = FStar_Options.unthrottle_inductives () in
          if uu____3534
          then fallback ()
          else
            (let uu____3536 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3536 with
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
                           | uu____3567 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3588 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3588
                         | uu____3591 ->
                             let uu____3592 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3592 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3597 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3641 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3654 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3661 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3662 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3679 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3696 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3698 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3698 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3716;
             FStar_Syntax_Syntax.vars = uu____3717;_},uu____3718)
          ->
          let uu____3739 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3739 FStar_Option.isNone
      | uu____3756 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3765 =
        let uu____3766 = FStar_Syntax_Util.un_uinst t in
        uu____3766.FStar_Syntax_Syntax.n in
      match uu____3765 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3769,uu____3770,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_3791  ->
                  match uu___115_3791 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3792 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3794 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3794 FStar_Option.isSome
      | uu____3811 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3820 = head_normal env t in
      if uu____3820
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
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
    let uu____3834 =
      let uu____3835 = FStar_Syntax_Syntax.null_binder t in [uu____3835] in
    let uu____3836 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3834 uu____3836 FStar_Pervasives_Native.None
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
                    let uu____3876 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3876
                | s ->
                    let uu____3881 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3881) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_3899  ->
    match uu___116_3899 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3900 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3939;
                       FStar_SMTEncoding_Term.rng = uu____3940;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3963) ->
              let uu____3972 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3983 -> false) args (FStar_List.rev xs)) in
              if uu____3972
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3987,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3991 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3995 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3995)) in
              if uu____3991
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3999 -> FStar_Pervasives_Native.None in
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
    | uu____4229 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____4234 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_4238  ->
    match uu___117_4238 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____4240 =
          let uu____4247 =
            let uu____4250 =
              let uu____4251 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____4251 in
            [uu____4250] in
          ("FStar.Char.Char", uu____4247) in
        FStar_SMTEncoding_Util.mkApp uu____4240
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____4274 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____4274
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4276) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____4292) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4295 =
          let uu____4296 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____4296 in
        failwith uu____4295
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4317 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4330 ->
            let uu____4337 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4337
        | uu____4338 ->
            if norm1
            then let uu____4339 = whnf env t1 in aux false uu____4339
            else
              (let uu____4341 =
                 let uu____4342 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4343 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4342 uu____4343 in
               failwith uu____4341) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____4375 ->
        let uu____4376 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4376)
let is_arithmetic_primitive:
  'Auu____4393 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4393 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4413::uu____4414::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4418::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4421 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4443 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4459 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4466 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4466)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4505)::uu____4506::uu____4507::[]) ->
          (((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_and_lid)
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_xor_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_or_lid))
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4558)::uu____4559::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4596 -> false
let rec encode_binders:
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
        (let uu____4805 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4805
         then
           let uu____4806 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4806
         else ());
        (let uu____4808 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4892  ->
                   fun b  ->
                     match uu____4892 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4971 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4987 = gen_term_var env1 x in
                           match uu____4987 with
                           | (xxsym,xx,env') ->
                               let uu____5011 =
                                 let uu____5016 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____5016 env1 xx in
                               (match uu____5011 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4971 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4808 with
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
          let uu____5175 = encode_term t env in
          match uu____5175 with
          | (t1,decls) ->
              let uu____5186 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____5186, decls)
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
          let uu____5197 = encode_term t env in
          match uu____5197 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5212 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____5212, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5214 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____5214, decls))
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
        let uu____5220 = encode_args args_e env in
        match uu____5220 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5239 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5248 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5248 in
            let binary arg_tms1 =
              let uu____5261 =
                let uu____5262 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5262 in
              let uu____5263 =
                let uu____5264 =
                  let uu____5265 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5265 in
                FStar_SMTEncoding_Term.unboxInt uu____5264 in
              (uu____5261, uu____5263) in
            let mk_default uu____5271 =
              let uu____5272 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5272 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5323 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5323
              then
                let uu____5324 = let uu____5325 = mk_args ts in op uu____5325 in
                FStar_All.pipe_right uu____5324 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5354 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5354
              then
                let uu____5355 = binary ts in
                match uu____5355 with
                | (t1,t2) ->
                    let uu____5362 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5362
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5366 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5366
                 then
                   let uu____5367 = op (binary ts) in
                   FStar_All.pipe_right uu____5367
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
            let uu____5498 =
              let uu____5507 =
                FStar_List.tryFind
                  (fun uu____5529  ->
                     match uu____5529 with
                     | (l,uu____5539) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5507 FStar_Util.must in
            (match uu____5498 with
             | (uu____5578,op) ->
                 let uu____5588 = op arg_tms in (uu____5588, decls))
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
        let uu____5596 = FStar_List.hd args_e in
        match uu____5596 with
        | (tm_sz,uu____5604) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5614 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5614 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5622 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5622);
                   t_decls) in
            let uu____5623 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5643::(sz_arg,uu____5645)::uu____5646::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5695 =
                    let uu____5698 = FStar_List.tail args_e in
                    FStar_List.tail uu____5698 in
                  let uu____5701 =
                    let uu____5704 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5704 in
                  (uu____5695, uu____5701)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5710::(sz_arg,uu____5712)::uu____5713::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5762 =
                    let uu____5763 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5763 in
                  failwith uu____5762
              | uu____5772 ->
                  let uu____5779 = FStar_List.tail args_e in
                  (uu____5779, FStar_Pervasives_Native.None) in
            (match uu____5623 with
             | (arg_tms,ext_sz) ->
                 let uu____5802 = encode_args arg_tms env in
                 (match uu____5802 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5823 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5832 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5832 in
                      let unary_arith arg_tms2 =
                        let uu____5841 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5841 in
                      let binary arg_tms2 =
                        let uu____5854 =
                          let uu____5855 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5855 in
                        let uu____5856 =
                          let uu____5857 =
                            let uu____5858 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5858 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5857 in
                        (uu____5854, uu____5856) in
                      let binary_arith arg_tms2 =
                        let uu____5873 =
                          let uu____5874 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5874 in
                        let uu____5875 =
                          let uu____5876 =
                            let uu____5877 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5877 in
                          FStar_SMTEncoding_Term.unboxInt uu____5876 in
                        (uu____5873, uu____5875) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5926 =
                          let uu____5927 = mk_args ts in op uu____5927 in
                        FStar_All.pipe_right uu____5926 resBox in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
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
                        let uu____6017 =
                          let uu____6020 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____6020 in
                        let uu____6022 =
                          let uu____6025 =
                            let uu____6026 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____6026 in
                          FStar_SMTEncoding_Term.boxBitVec uu____6025 in
                        mk_bv uu____6017 unary uu____6022 arg_tms2 in
                      let to_int =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz) in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____6201 =
                        let uu____6210 =
                          FStar_List.tryFind
                            (fun uu____6232  ->
                               match uu____6232 with
                               | (l,uu____6242) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6210 FStar_Util.must in
                      (match uu____6201 with
                       | (uu____6283,op) ->
                           let uu____6293 = op arg_tms1 in
                           (uu____6293, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6304 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6304
       then
         let uu____6305 = FStar_Syntax_Print.tag_of_term t in
         let uu____6306 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6307 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6305 uu____6306
           uu____6307
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6313 ->
           let uu____6338 =
             let uu____6339 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6340 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6341 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6342 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6339
               uu____6340 uu____6341 uu____6342 in
           failwith uu____6338
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6347 =
             let uu____6348 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6349 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6350 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6351 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6348
               uu____6349 uu____6350 uu____6351 in
           failwith uu____6347
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6357 =
             let uu____6358 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6358 in
           failwith uu____6357
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6365) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6407) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6417 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6417, [])
       | FStar_Syntax_Syntax.Tm_type uu____6420 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6424) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6430 = encode_const c in (uu____6430, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6452 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6452 with
            | (binders1,res) ->
                let uu____6463 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6463
                then
                  let uu____6468 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6468 with
                   | (vars,guards,env',decls,uu____6493) ->
                       let fsym =
                         let uu____6511 = varops.fresh "f" in
                         (uu____6511, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6514 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_6523 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_6523.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_6523.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_6523.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_6523.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_6523.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_6523.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_6523.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_6523.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_6523.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_6523.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_6523.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_6523.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_6523.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_6523.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_6523.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_6523.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_6523.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_6523.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_6523.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___141_6523.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___141_6523.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_6523.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_6523.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_6523.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_6523.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___141_6523.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___141_6523.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___141_6523.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___141_6523.FStar_TypeChecker_Env.identifier_info)
                            }) res in
                       (match uu____6514 with
                        | (pre_opt,res_t) ->
                            let uu____6534 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6534 with
                             | (res_pred,decls') ->
                                 let uu____6545 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6558 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6558, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6562 =
                                         encode_formula pre env' in
                                       (match uu____6562 with
                                        | (guard,decls0) ->
                                            let uu____6575 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6575, decls0)) in
                                 (match uu____6545 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6587 =
                                          let uu____6598 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6598) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6587 in
                                      let cvars =
                                        let uu____6616 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6616
                                          (FStar_List.filter
                                             (fun uu____6630  ->
                                                match uu____6630 with
                                                | (x,uu____6636) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6655 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6655 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6663 =
                                             let uu____6664 =
                                               let uu____6671 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6671) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6664 in
                                           (uu____6663,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6691 =
                                               let uu____6692 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6692 in
                                             varops.mk_unique uu____6691 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6703 =
                                               FStar_Options.log_queries () in
                                             if uu____6703
                                             then
                                               let uu____6706 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6706
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6714 =
                                               let uu____6721 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6721) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6714 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6733 =
                                               let uu____6740 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6740,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6733 in
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
                                             let uu____6761 =
                                               let uu____6768 =
                                                 let uu____6769 =
                                                   let uu____6780 =
                                                     let uu____6781 =
                                                       let uu____6786 =
                                                         let uu____6787 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6787 in
                                                       (f_has_t, uu____6786) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6781 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6780) in
                                                 mkForall_fuel uu____6769 in
                                               (uu____6768,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6761 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6810 =
                                               let uu____6817 =
                                                 let uu____6818 =
                                                   let uu____6829 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6829) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6818 in
                                               (uu____6817,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6810 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6854 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6854);
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
                     let uu____6869 =
                       let uu____6876 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6876,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6869 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6888 =
                       let uu____6895 =
                         let uu____6896 =
                           let uu____6907 =
                             let uu____6908 =
                               let uu____6913 =
                                 let uu____6914 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6914 in
                               (f_has_t, uu____6913) in
                             FStar_SMTEncoding_Util.mkImp uu____6908 in
                           ([[f_has_t]], [fsym], uu____6907) in
                         mkForall_fuel uu____6896 in
                       (uu____6895, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6888 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6941 ->
           let uu____6948 =
             let uu____6953 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6953 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6960;
                 FStar_Syntax_Syntax.vars = uu____6961;_} ->
                 let uu____6968 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6968 with
                  | (b,f1) ->
                      let uu____6993 =
                        let uu____6994 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6994 in
                      (uu____6993, f1))
             | uu____7003 -> failwith "impossible" in
           (match uu____6948 with
            | (x,f) ->
                let uu____7014 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____7014 with
                 | (base_t,decls) ->
                     let uu____7025 = gen_term_var env x in
                     (match uu____7025 with
                      | (x1,xtm,env') ->
                          let uu____7039 = encode_formula f env' in
                          (match uu____7039 with
                           | (refinement,decls') ->
                               let uu____7050 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____7050 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____7066 =
                                        let uu____7069 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____7076 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____7069
                                          uu____7076 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7066 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7109  ->
                                              match uu____7109 with
                                              | (y,uu____7115) ->
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
                                    let uu____7148 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7148 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7156 =
                                           let uu____7157 =
                                             let uu____7164 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7164) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7157 in
                                         (uu____7156,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7185 =
                                             let uu____7186 =
                                               let uu____7187 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7187 in
                                             Prims.strcat module_name
                                               uu____7186 in
                                           varops.mk_unique uu____7185 in
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
                                           let uu____7201 =
                                             let uu____7208 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7208) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7201 in
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
                                           let uu____7223 =
                                             let uu____7230 =
                                               let uu____7231 =
                                                 let uu____7242 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7242) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7231 in
                                             (uu____7230,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7223 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7268 =
                                             let uu____7275 =
                                               let uu____7276 =
                                                 let uu____7287 =
                                                   let uu____7288 =
                                                     let uu____7293 =
                                                       let uu____7294 =
                                                         let uu____7305 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7305) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7294 in
                                                     (uu____7293, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7288 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7287) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7276 in
                                             (uu____7275,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7268 in
                                         let t_kinding =
                                           let uu____7343 =
                                             let uu____7350 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7350,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7343 in
                                         let t_interp =
                                           let uu____7368 =
                                             let uu____7375 =
                                               let uu____7376 =
                                                 let uu____7387 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7387) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7376 in
                                             let uu____7410 =
                                               let uu____7413 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7413 in
                                             (uu____7375, uu____7410,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7368 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7420 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7420);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7450 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7450 in
           let uu____7451 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7451 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7463 =
                    let uu____7470 =
                      let uu____7471 =
                        let uu____7472 =
                          let uu____7473 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7473 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7472 in
                      varops.mk_unique uu____7471 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7470) in
                  FStar_SMTEncoding_Util.mkAssume uu____7463 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7478 ->
           let uu____7493 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7493 with
            | (head1,args_e) ->
                let uu____7534 =
                  let uu____7547 =
                    let uu____7548 = FStar_Syntax_Subst.compress head1 in
                    uu____7548.FStar_Syntax_Syntax.n in
                  (uu____7547, args_e) in
                (match uu____7534 with
                 | uu____7563 when head_redex env head1 ->
                     let uu____7576 = whnf env t in
                     encode_term uu____7576 env
                 | uu____7577 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7596 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7610;
                       FStar_Syntax_Syntax.vars = uu____7611;_},uu____7612),uu____7613::
                    (v1,uu____7615)::(v2,uu____7617)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7668 = encode_term v1 env in
                     (match uu____7668 with
                      | (v11,decls1) ->
                          let uu____7679 = encode_term v2 env in
                          (match uu____7679 with
                           | (v21,decls2) ->
                               let uu____7690 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7690,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7694::(v1,uu____7696)::(v2,uu____7698)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7745 = encode_term v1 env in
                     (match uu____7745 with
                      | (v11,decls1) ->
                          let uu____7756 = encode_term v2 env in
                          (match uu____7756 with
                           | (v21,decls2) ->
                               let uu____7767 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7767,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7770) ->
                     let e0 =
                       let uu____7788 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7788 in
                     ((let uu____7796 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7796
                       then
                         let uu____7797 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7797
                       else ());
                      (let e =
                         let uu____7802 =
                           let uu____7803 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7804 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7803
                             uu____7804 in
                         uu____7802 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7813),(arg,uu____7815)::[]) -> encode_term arg env
                 | uu____7840 ->
                     let uu____7853 = encode_args args_e env in
                     (match uu____7853 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7908 = encode_term head1 env in
                            match uu____7908 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7972 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7972 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8050  ->
                                                 fun uu____8051  ->
                                                   match (uu____8050,
                                                           uu____8051)
                                                   with
                                                   | ((bv,uu____8073),
                                                      (a,uu____8075)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____8093 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____8093
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____8098 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____8098 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____8113 =
                                                   let uu____8120 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____8129 =
                                                     let uu____8130 =
                                                       let uu____8131 =
                                                         let uu____8132 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____8132 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8131 in
                                                     varops.mk_unique
                                                       uu____8130 in
                                                   (uu____8120,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8129) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8113 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8149 = lookup_free_var_sym env fv in
                            match uu____8149 with
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
                                   FStar_Syntax_Syntax.pos = uu____8180;
                                   FStar_Syntax_Syntax.vars = uu____8181;_},uu____8182)
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
                                   FStar_Syntax_Syntax.pos = uu____8193;
                                   FStar_Syntax_Syntax.vars = uu____8194;_},uu____8195)
                                ->
                                let uu____8200 =
                                  let uu____8201 =
                                    let uu____8206 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8206
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8201
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8200
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8236 =
                                  let uu____8237 =
                                    let uu____8242 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8242
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8237
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8236
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8271,(FStar_Util.Inl t1,uu____8273),uu____8274)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8323,(FStar_Util.Inr c,uu____8325),uu____8326)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8375 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8402 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8402 in
                               let uu____8403 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8403 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8419;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8420;_},uu____8421)
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
                                     | uu____8435 ->
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
           let uu____8484 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8484 with
            | (bs1,body1,opening) ->
                let fallback uu____8507 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8514 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8514, [decl]) in
                let is_impure rc =
                  let uu____8521 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8521 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8531 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8531
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8551 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8551
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8555 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8555)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8562 =
                         let uu____8563 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8563 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8562);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8565 =
                       (is_impure rc) &&
                         (let uu____8567 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8567) in
                     if uu____8565
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8574 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8574 with
                        | (vars,guards,envbody,decls,uu____8599) ->
                            let body2 =
                              let uu____8613 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8613
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8615 = encode_term body2 envbody in
                            (match uu____8615 with
                             | (body3,decls') ->
                                 let uu____8626 =
                                   let uu____8635 = codomain_eff rc in
                                   match uu____8635 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8654 = encode_term tfun env in
                                       (match uu____8654 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8626 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8686 =
                                          let uu____8697 =
                                            let uu____8698 =
                                              let uu____8703 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8703, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8698 in
                                          ([], vars, uu____8697) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8686 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8715 =
                                              let uu____8718 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8718
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8715 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8737 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8737 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8745 =
                                             let uu____8746 =
                                               let uu____8753 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8753) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8746 in
                                           (uu____8745,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8764 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8764 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8775 =
                                                    let uu____8776 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8776 = cache_size in
                                                  if uu____8775
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
                                                    let uu____8792 =
                                                      let uu____8793 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8793 in
                                                    varops.mk_unique
                                                      uu____8792 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8800 =
                                                    let uu____8807 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8807) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8800 in
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
                                                      let uu____8825 =
                                                        let uu____8826 =
                                                          let uu____8833 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8833,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8826 in
                                                      [uu____8825] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8846 =
                                                    let uu____8853 =
                                                      let uu____8854 =
                                                        let uu____8865 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8865) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8854 in
                                                    (uu____8853,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8846 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8882 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8882);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8885,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8886;
                          FStar_Syntax_Syntax.lbunivs = uu____8887;
                          FStar_Syntax_Syntax.lbtyp = uu____8888;
                          FStar_Syntax_Syntax.lbeff = uu____8889;
                          FStar_Syntax_Syntax.lbdef = uu____8890;_}::uu____8891),uu____8892)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8918;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8920;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8941 ->
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
              let uu____9011 = encode_term e1 env in
              match uu____9011 with
              | (ee1,decls1) ->
                  let uu____9022 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9022 with
                   | (xs,e21) ->
                       let uu____9047 = FStar_List.hd xs in
                       (match uu____9047 with
                        | (x1,uu____9061) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9063 = encode_body e21 env' in
                            (match uu____9063 with
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
            let uu____9095 =
              let uu____9102 =
                let uu____9103 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9103 in
              gen_term_var env uu____9102 in
            match uu____9095 with
            | (scrsym,scr',env1) ->
                let uu____9111 = encode_term e env1 in
                (match uu____9111 with
                 | (scr,decls) ->
                     let uu____9122 =
                       let encode_branch b uu____9147 =
                         match uu____9147 with
                         | (else_case,decls1) ->
                             let uu____9166 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9166 with
                              | (p,w,br) ->
                                  let uu____9192 = encode_pat env1 p in
                                  (match uu____9192 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9229  ->
                                                   match uu____9229 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9236 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9258 =
                                               encode_term w1 env2 in
                                             (match uu____9258 with
                                              | (w2,decls2) ->
                                                  let uu____9271 =
                                                    let uu____9272 =
                                                      let uu____9277 =
                                                        let uu____9278 =
                                                          let uu____9283 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9283) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9278 in
                                                      (guard, uu____9277) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9272 in
                                                  (uu____9271, decls2)) in
                                       (match uu____9236 with
                                        | (guard1,decls2) ->
                                            let uu____9296 =
                                              encode_br br env2 in
                                            (match uu____9296 with
                                             | (br1,decls3) ->
                                                 let uu____9309 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9309,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9122 with
                      | (match_tm,decls1) ->
                          let uu____9328 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9328, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9368 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9368
       then
         let uu____9369 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9369
       else ());
      (let uu____9371 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9371 with
       | (vars,pat_term) ->
           let uu____9388 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9441  ->
                     fun v1  ->
                       match uu____9441 with
                       | (env1,vars1) ->
                           let uu____9493 = gen_term_var env1 v1 in
                           (match uu____9493 with
                            | (xx,uu____9515,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9388 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9594 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9595 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9596 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9604 =
                        let uu____9609 = encode_const c in
                        (scrutinee, uu____9609) in
                      FStar_SMTEncoding_Util.mkEq uu____9604
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9630 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9630 with
                        | (uu____9637,uu____9638::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9641 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9674  ->
                                  match uu____9674 with
                                  | (arg,uu____9682) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9688 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9688)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9715) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9746 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9769 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9813  ->
                                  match uu____9813 with
                                  | (arg,uu____9827) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9833 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9833)) in
                      FStar_All.pipe_right uu____9769 FStar_List.flatten in
                let pat_term1 uu____9861 = encode_term pat_term env1 in
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
      let uu____9871 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9909  ->
                fun uu____9910  ->
                  match (uu____9909, uu____9910) with
                  | ((tms,decls),(t,uu____9946)) ->
                      let uu____9967 = encode_term t env in
                      (match uu____9967 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9871 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10024 = FStar_Syntax_Util.list_elements e in
        match uu____10024 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____10045 =
          let uu____10060 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10060 FStar_Syntax_Util.head_and_args in
        match uu____10045 with
        | (head1,args) ->
            let uu____10099 =
              let uu____10112 =
                let uu____10113 = FStar_Syntax_Util.un_uinst head1 in
                uu____10113.FStar_Syntax_Syntax.n in
              (uu____10112, args) in
            (match uu____10099 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10127,uu____10128)::(e,uu____10130)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10165 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10201 =
            let uu____10216 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10216 FStar_Syntax_Util.head_and_args in
          match uu____10201 with
          | (head1,args) ->
              let uu____10257 =
                let uu____10270 =
                  let uu____10271 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10271.FStar_Syntax_Syntax.n in
                (uu____10270, args) in
              (match uu____10257 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10288)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10315 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10337 = smt_pat_or1 t1 in
            (match uu____10337 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10353 = list_elements1 e in
                 FStar_All.pipe_right uu____10353
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10371 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10371
                           (FStar_List.map one_pat)))
             | uu____10382 ->
                 let uu____10387 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10387])
        | uu____10408 ->
            let uu____10411 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10411] in
      let uu____10432 =
        let uu____10451 =
          let uu____10452 = FStar_Syntax_Subst.compress t in
          uu____10452.FStar_Syntax_Syntax.n in
        match uu____10451 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10491 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10491 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10534;
                        FStar_Syntax_Syntax.effect_name = uu____10535;
                        FStar_Syntax_Syntax.result_typ = uu____10536;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10538)::(post,uu____10540)::(pats,uu____10542)::[];
                        FStar_Syntax_Syntax.flags = uu____10543;_}
                      ->
                      let uu____10584 = lemma_pats pats in
                      (binders1, pre, post, uu____10584)
                  | uu____10601 -> failwith "impos"))
        | uu____10620 -> failwith "Impos" in
      match uu____10432 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___142_10668 = env in
            {
              bindings = (uu___142_10668.bindings);
              depth = (uu___142_10668.depth);
              tcenv = (uu___142_10668.tcenv);
              warn = (uu___142_10668.warn);
              cache = (uu___142_10668.cache);
              nolabels = (uu___142_10668.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___142_10668.encode_non_total_function_typ);
              current_module_name = (uu___142_10668.current_module_name)
            } in
          let uu____10669 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10669 with
           | (vars,guards,env2,decls,uu____10694) ->
               let uu____10707 =
                 let uu____10720 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10764 =
                             let uu____10773 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10773
                               FStar_List.unzip in
                           match uu____10764 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10720 FStar_List.unzip in
               (match uu____10707 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___143_10882 = env2 in
                      {
                        bindings = (uu___143_10882.bindings);
                        depth = (uu___143_10882.depth);
                        tcenv = (uu___143_10882.tcenv);
                        warn = (uu___143_10882.warn);
                        cache = (uu___143_10882.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___143_10882.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___143_10882.encode_non_total_function_typ);
                        current_module_name =
                          (uu___143_10882.current_module_name)
                      } in
                    let uu____10883 =
                      let uu____10888 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10888 env3 in
                    (match uu____10883 with
                     | (pre1,decls'') ->
                         let uu____10895 =
                           let uu____10900 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10900 env3 in
                         (match uu____10895 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10910 =
                                let uu____10911 =
                                  let uu____10922 =
                                    let uu____10923 =
                                      let uu____10928 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10928, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10923 in
                                  (pats, vars, uu____10922) in
                                FStar_SMTEncoding_Util.mkForall uu____10911 in
                              (uu____10910, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10947 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10947
        then
          let uu____10948 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10949 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10948 uu____10949
        else () in
      let enc f r l =
        let uu____10982 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11010 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11010 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10982 with
        | (decls,args) ->
            let uu____11039 =
              let uu___144_11040 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_11040.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_11040.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11039, decls) in
      let const_op f r uu____11071 =
        let uu____11084 = f r in (uu____11084, []) in
      let un_op f l =
        let uu____11103 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11103 in
      let bin_op f uu___118_11119 =
        match uu___118_11119 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11130 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11164 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11187  ->
                 match uu____11187 with
                 | (t,uu____11201) ->
                     let uu____11202 = encode_formula t env in
                     (match uu____11202 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11164 with
        | (decls,phis) ->
            let uu____11231 =
              let uu___145_11232 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_11232.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_11232.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11231, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11293  ->
               match uu____11293 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11312) -> false
                    | uu____11313 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11328 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11328
        else
          (let uu____11342 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11342 r rf) in
      let mk_imp1 r uu___119_11367 =
        match uu___119_11367 with
        | (lhs,uu____11373)::(rhs,uu____11375)::[] ->
            let uu____11402 = encode_formula rhs env in
            (match uu____11402 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11417) ->
                      (l1, decls1)
                  | uu____11422 ->
                      let uu____11423 = encode_formula lhs env in
                      (match uu____11423 with
                       | (l2,decls2) ->
                           let uu____11434 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11434, (FStar_List.append decls1 decls2)))))
        | uu____11437 -> failwith "impossible" in
      let mk_ite r uu___120_11458 =
        match uu___120_11458 with
        | (guard,uu____11464)::(_then,uu____11466)::(_else,uu____11468)::[]
            ->
            let uu____11505 = encode_formula guard env in
            (match uu____11505 with
             | (g,decls1) ->
                 let uu____11516 = encode_formula _then env in
                 (match uu____11516 with
                  | (t,decls2) ->
                      let uu____11527 = encode_formula _else env in
                      (match uu____11527 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11541 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11566 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11566 in
      let connectives =
        let uu____11584 =
          let uu____11597 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11597) in
        let uu____11614 =
          let uu____11629 =
            let uu____11642 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11642) in
          let uu____11659 =
            let uu____11674 =
              let uu____11689 =
                let uu____11702 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11702) in
              let uu____11719 =
                let uu____11734 =
                  let uu____11749 =
                    let uu____11762 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11762) in
                  [uu____11749;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11734 in
              uu____11689 :: uu____11719 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11674 in
          uu____11629 :: uu____11659 in
        uu____11584 :: uu____11614 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12083 = encode_formula phi' env in
            (match uu____12083 with
             | (phi2,decls) ->
                 let uu____12094 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12094, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12095 ->
            let uu____12102 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12102 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12141 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12141 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12153;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12155;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12176 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12176 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12223::(x,uu____12225)::(t,uu____12227)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12274 = encode_term x env in
                 (match uu____12274 with
                  | (x1,decls) ->
                      let uu____12285 = encode_term t env in
                      (match uu____12285 with
                       | (t1,decls') ->
                           let uu____12296 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12296, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12301)::(msg,uu____12303)::(phi2,uu____12305)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12350 =
                   let uu____12355 =
                     let uu____12356 = FStar_Syntax_Subst.compress r in
                     uu____12356.FStar_Syntax_Syntax.n in
                   let uu____12359 =
                     let uu____12360 = FStar_Syntax_Subst.compress msg in
                     uu____12360.FStar_Syntax_Syntax.n in
                   (uu____12355, uu____12359) in
                 (match uu____12350 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12369))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12375 -> fallback phi2)
             | uu____12380 when head_redex env head2 ->
                 let uu____12393 = whnf env phi1 in
                 encode_formula uu____12393 env
             | uu____12394 ->
                 let uu____12407 = encode_term phi1 env in
                 (match uu____12407 with
                  | (tt,decls) ->
                      let uu____12418 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___146_12421 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___146_12421.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___146_12421.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12418, decls)))
        | uu____12422 ->
            let uu____12423 = encode_term phi1 env in
            (match uu____12423 with
             | (tt,decls) ->
                 let uu____12434 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___147_12437 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___147_12437.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___147_12437.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12434, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12473 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12473 with
        | (vars,guards,env2,decls,uu____12512) ->
            let uu____12525 =
              let uu____12538 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12586 =
                          let uu____12595 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12625  ->
                                    match uu____12625 with
                                    | (t,uu____12635) ->
                                        encode_term t
                                          (let uu___148_12637 = env2 in
                                           {
                                             bindings =
                                               (uu___148_12637.bindings);
                                             depth = (uu___148_12637.depth);
                                             tcenv = (uu___148_12637.tcenv);
                                             warn = (uu___148_12637.warn);
                                             cache = (uu___148_12637.cache);
                                             nolabels =
                                               (uu___148_12637.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___148_12637.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___148_12637.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12595 FStar_List.unzip in
                        match uu____12586 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12538 FStar_List.unzip in
            (match uu____12525 with
             | (pats,decls') ->
                 let uu____12736 = encode_formula body env2 in
                 (match uu____12736 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12768;
                             FStar_SMTEncoding_Term.rng = uu____12769;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12784 -> guards in
                      let uu____12789 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12789, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12849  ->
                   match uu____12849 with
                   | (x,uu____12855) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12863 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12875 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12875) uu____12863 tl1 in
             let uu____12878 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12905  ->
                       match uu____12905 with
                       | (b,uu____12911) ->
                           let uu____12912 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12912)) in
             (match uu____12878 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12918) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12932 =
                    let uu____12933 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12933 in
                  FStar_Errors.warn pos uu____12932) in
       let uu____12934 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12934 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12943 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13001  ->
                     match uu____13001 with
                     | (l,uu____13015) -> FStar_Ident.lid_equals op l)) in
           (match uu____12943 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13048,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13088 = encode_q_body env vars pats body in
             match uu____13088 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13133 =
                     let uu____13144 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13144) in
                   FStar_SMTEncoding_Term.mkForall uu____13133
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13163 = encode_q_body env vars pats body in
             match uu____13163 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13207 =
                   let uu____13208 =
                     let uu____13219 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13219) in
                   FStar_SMTEncoding_Term.mkExists uu____13208
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13207, decls))))
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
  let uu____13317 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13317 with
  | (asym,a) ->
      let uu____13324 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13324 with
       | (xsym,x) ->
           let uu____13331 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13331 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13375 =
                      let uu____13386 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13386, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13375 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13412 =
                      let uu____13419 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13419) in
                    FStar_SMTEncoding_Util.mkApp uu____13412 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13432 =
                    let uu____13435 =
                      let uu____13438 =
                        let uu____13441 =
                          let uu____13442 =
                            let uu____13449 =
                              let uu____13450 =
                                let uu____13461 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13461) in
                              FStar_SMTEncoding_Util.mkForall uu____13450 in
                            (uu____13449, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13442 in
                        let uu____13478 =
                          let uu____13481 =
                            let uu____13482 =
                              let uu____13489 =
                                let uu____13490 =
                                  let uu____13501 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13501) in
                                FStar_SMTEncoding_Util.mkForall uu____13490 in
                              (uu____13489,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13482 in
                          [uu____13481] in
                        uu____13441 :: uu____13478 in
                      xtok_decl :: uu____13438 in
                    xname_decl :: uu____13435 in
                  (xtok1, uu____13432) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13592 =
                    let uu____13605 =
                      let uu____13614 =
                        let uu____13615 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13615 in
                      quant axy uu____13614 in
                    (FStar_Parser_Const.op_Eq, uu____13605) in
                  let uu____13624 =
                    let uu____13639 =
                      let uu____13652 =
                        let uu____13661 =
                          let uu____13662 =
                            let uu____13663 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13663 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13662 in
                        quant axy uu____13661 in
                      (FStar_Parser_Const.op_notEq, uu____13652) in
                    let uu____13672 =
                      let uu____13687 =
                        let uu____13700 =
                          let uu____13709 =
                            let uu____13710 =
                              let uu____13711 =
                                let uu____13716 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13717 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13716, uu____13717) in
                              FStar_SMTEncoding_Util.mkLT uu____13711 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13710 in
                          quant xy uu____13709 in
                        (FStar_Parser_Const.op_LT, uu____13700) in
                      let uu____13726 =
                        let uu____13741 =
                          let uu____13754 =
                            let uu____13763 =
                              let uu____13764 =
                                let uu____13765 =
                                  let uu____13770 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13771 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13770, uu____13771) in
                                FStar_SMTEncoding_Util.mkLTE uu____13765 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13764 in
                            quant xy uu____13763 in
                          (FStar_Parser_Const.op_LTE, uu____13754) in
                        let uu____13780 =
                          let uu____13795 =
                            let uu____13808 =
                              let uu____13817 =
                                let uu____13818 =
                                  let uu____13819 =
                                    let uu____13824 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13825 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13824, uu____13825) in
                                  FStar_SMTEncoding_Util.mkGT uu____13819 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13818 in
                              quant xy uu____13817 in
                            (FStar_Parser_Const.op_GT, uu____13808) in
                          let uu____13834 =
                            let uu____13849 =
                              let uu____13862 =
                                let uu____13871 =
                                  let uu____13872 =
                                    let uu____13873 =
                                      let uu____13878 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13879 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13878, uu____13879) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13873 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13872 in
                                quant xy uu____13871 in
                              (FStar_Parser_Const.op_GTE, uu____13862) in
                            let uu____13888 =
                              let uu____13903 =
                                let uu____13916 =
                                  let uu____13925 =
                                    let uu____13926 =
                                      let uu____13927 =
                                        let uu____13932 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13933 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13932, uu____13933) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13927 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13926 in
                                  quant xy uu____13925 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13916) in
                              let uu____13942 =
                                let uu____13957 =
                                  let uu____13970 =
                                    let uu____13979 =
                                      let uu____13980 =
                                        let uu____13981 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13981 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13980 in
                                    quant qx uu____13979 in
                                  (FStar_Parser_Const.op_Minus, uu____13970) in
                                let uu____13990 =
                                  let uu____14005 =
                                    let uu____14018 =
                                      let uu____14027 =
                                        let uu____14028 =
                                          let uu____14029 =
                                            let uu____14034 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14035 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14034, uu____14035) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14029 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14028 in
                                      quant xy uu____14027 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14018) in
                                  let uu____14044 =
                                    let uu____14059 =
                                      let uu____14072 =
                                        let uu____14081 =
                                          let uu____14082 =
                                            let uu____14083 =
                                              let uu____14088 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14089 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14088, uu____14089) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14083 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14082 in
                                        quant xy uu____14081 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14072) in
                                    let uu____14098 =
                                      let uu____14113 =
                                        let uu____14126 =
                                          let uu____14135 =
                                            let uu____14136 =
                                              let uu____14137 =
                                                let uu____14142 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14143 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14142, uu____14143) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14137 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14136 in
                                          quant xy uu____14135 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14126) in
                                      let uu____14152 =
                                        let uu____14167 =
                                          let uu____14180 =
                                            let uu____14189 =
                                              let uu____14190 =
                                                let uu____14191 =
                                                  let uu____14196 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14197 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14196, uu____14197) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14191 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14190 in
                                            quant xy uu____14189 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14180) in
                                        let uu____14206 =
                                          let uu____14221 =
                                            let uu____14234 =
                                              let uu____14243 =
                                                let uu____14244 =
                                                  let uu____14245 =
                                                    let uu____14250 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14251 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14250,
                                                      uu____14251) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14245 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14244 in
                                              quant xy uu____14243 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14234) in
                                          let uu____14260 =
                                            let uu____14275 =
                                              let uu____14288 =
                                                let uu____14297 =
                                                  let uu____14298 =
                                                    let uu____14299 =
                                                      let uu____14304 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14305 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14304,
                                                        uu____14305) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14299 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14298 in
                                                quant xy uu____14297 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14288) in
                                            let uu____14314 =
                                              let uu____14329 =
                                                let uu____14342 =
                                                  let uu____14351 =
                                                    let uu____14352 =
                                                      let uu____14353 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14353 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14352 in
                                                  quant qx uu____14351 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14342) in
                                              [uu____14329] in
                                            uu____14275 :: uu____14314 in
                                          uu____14221 :: uu____14260 in
                                        uu____14167 :: uu____14206 in
                                      uu____14113 :: uu____14152 in
                                    uu____14059 :: uu____14098 in
                                  uu____14005 :: uu____14044 in
                                uu____13957 :: uu____13990 in
                              uu____13903 :: uu____13942 in
                            uu____13849 :: uu____13888 in
                          uu____13795 :: uu____13834 in
                        uu____13741 :: uu____13780 in
                      uu____13687 :: uu____13726 in
                    uu____13639 :: uu____13672 in
                  uu____13592 :: uu____13624 in
                let mk1 l v1 =
                  let uu____14567 =
                    let uu____14576 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14634  ->
                              match uu____14634 with
                              | (l',uu____14648) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14576
                      (FStar_Option.map
                         (fun uu____14708  ->
                            match uu____14708 with | (uu____14727,b) -> b v1)) in
                  FStar_All.pipe_right uu____14567 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14798  ->
                          match uu____14798 with
                          | (l',uu____14812) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14853 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14853 with
        | (xxsym,xx) ->
            let uu____14860 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14860 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14870 =
                   let uu____14877 =
                     let uu____14878 =
                       let uu____14889 =
                         let uu____14890 =
                           let uu____14895 =
                             let uu____14896 =
                               let uu____14901 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14901) in
                             FStar_SMTEncoding_Util.mkEq uu____14896 in
                           (xx_has_type, uu____14895) in
                         FStar_SMTEncoding_Util.mkImp uu____14890 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14889) in
                     FStar_SMTEncoding_Util.mkForall uu____14878 in
                   let uu____14926 =
                     let uu____14927 =
                       let uu____14928 =
                         let uu____14929 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14929 in
                       Prims.strcat module_name uu____14928 in
                     varops.mk_unique uu____14927 in
                   (uu____14877, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14926) in
                 FStar_SMTEncoding_Util.mkAssume uu____14870)
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
    let uu____14969 =
      let uu____14970 =
        let uu____14977 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14977, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14970 in
    let uu____14980 =
      let uu____14983 =
        let uu____14984 =
          let uu____14991 =
            let uu____14992 =
              let uu____15003 =
                let uu____15004 =
                  let uu____15009 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15009) in
                FStar_SMTEncoding_Util.mkImp uu____15004 in
              ([[typing_pred]], [xx], uu____15003) in
            mkForall_fuel uu____14992 in
          (uu____14991, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14984 in
      [uu____14983] in
    uu____14969 :: uu____14980 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15051 =
      let uu____15052 =
        let uu____15059 =
          let uu____15060 =
            let uu____15071 =
              let uu____15076 =
                let uu____15079 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15079] in
              [uu____15076] in
            let uu____15084 =
              let uu____15085 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15085 tt in
            (uu____15071, [bb], uu____15084) in
          FStar_SMTEncoding_Util.mkForall uu____15060 in
        (uu____15059, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15052 in
    let uu____15106 =
      let uu____15109 =
        let uu____15110 =
          let uu____15117 =
            let uu____15118 =
              let uu____15129 =
                let uu____15130 =
                  let uu____15135 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15135) in
                FStar_SMTEncoding_Util.mkImp uu____15130 in
              ([[typing_pred]], [xx], uu____15129) in
            mkForall_fuel uu____15118 in
          (uu____15117, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15110 in
      [uu____15109] in
    uu____15051 :: uu____15106 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15185 =
        let uu____15186 =
          let uu____15193 =
            let uu____15196 =
              let uu____15199 =
                let uu____15202 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15203 =
                  let uu____15206 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15206] in
                uu____15202 :: uu____15203 in
              tt :: uu____15199 in
            tt :: uu____15196 in
          ("Prims.Precedes", uu____15193) in
        FStar_SMTEncoding_Util.mkApp uu____15186 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15185 in
    let precedes_y_x =
      let uu____15210 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15210 in
    let uu____15213 =
      let uu____15214 =
        let uu____15221 =
          let uu____15222 =
            let uu____15233 =
              let uu____15238 =
                let uu____15241 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15241] in
              [uu____15238] in
            let uu____15246 =
              let uu____15247 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15247 tt in
            (uu____15233, [bb], uu____15246) in
          FStar_SMTEncoding_Util.mkForall uu____15222 in
        (uu____15221, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15214 in
    let uu____15268 =
      let uu____15271 =
        let uu____15272 =
          let uu____15279 =
            let uu____15280 =
              let uu____15291 =
                let uu____15292 =
                  let uu____15297 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15297) in
                FStar_SMTEncoding_Util.mkImp uu____15292 in
              ([[typing_pred]], [xx], uu____15291) in
            mkForall_fuel uu____15280 in
          (uu____15279, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15272 in
      let uu____15322 =
        let uu____15325 =
          let uu____15326 =
            let uu____15333 =
              let uu____15334 =
                let uu____15345 =
                  let uu____15346 =
                    let uu____15351 =
                      let uu____15352 =
                        let uu____15355 =
                          let uu____15358 =
                            let uu____15361 =
                              let uu____15362 =
                                let uu____15367 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15368 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15367, uu____15368) in
                              FStar_SMTEncoding_Util.mkGT uu____15362 in
                            let uu____15369 =
                              let uu____15372 =
                                let uu____15373 =
                                  let uu____15378 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15379 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15378, uu____15379) in
                                FStar_SMTEncoding_Util.mkGTE uu____15373 in
                              let uu____15380 =
                                let uu____15383 =
                                  let uu____15384 =
                                    let uu____15389 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15390 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15389, uu____15390) in
                                  FStar_SMTEncoding_Util.mkLT uu____15384 in
                                [uu____15383] in
                              uu____15372 :: uu____15380 in
                            uu____15361 :: uu____15369 in
                          typing_pred_y :: uu____15358 in
                        typing_pred :: uu____15355 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15352 in
                    (uu____15351, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15346 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15345) in
              mkForall_fuel uu____15334 in
            (uu____15333,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15326 in
        [uu____15325] in
      uu____15271 :: uu____15322 in
    uu____15213 :: uu____15268 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15436 =
      let uu____15437 =
        let uu____15444 =
          let uu____15445 =
            let uu____15456 =
              let uu____15461 =
                let uu____15464 = FStar_SMTEncoding_Term.boxString b in
                [uu____15464] in
              [uu____15461] in
            let uu____15469 =
              let uu____15470 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15470 tt in
            (uu____15456, [bb], uu____15469) in
          FStar_SMTEncoding_Util.mkForall uu____15445 in
        (uu____15444, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15437 in
    let uu____15491 =
      let uu____15494 =
        let uu____15495 =
          let uu____15502 =
            let uu____15503 =
              let uu____15514 =
                let uu____15515 =
                  let uu____15520 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15520) in
                FStar_SMTEncoding_Util.mkImp uu____15515 in
              ([[typing_pred]], [xx], uu____15514) in
            mkForall_fuel uu____15503 in
          (uu____15502, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15495 in
      [uu____15494] in
    uu____15436 :: uu____15491 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15573 =
      let uu____15574 =
        let uu____15581 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15581, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15574 in
    [uu____15573] in
  let mk_and_interp env conj uu____15593 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15618 =
      let uu____15619 =
        let uu____15626 =
          let uu____15627 =
            let uu____15638 =
              let uu____15639 =
                let uu____15644 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15644, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15639 in
            ([[l_and_a_b]], [aa; bb], uu____15638) in
          FStar_SMTEncoding_Util.mkForall uu____15627 in
        (uu____15626, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15619 in
    [uu____15618] in
  let mk_or_interp env disj uu____15682 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15707 =
      let uu____15708 =
        let uu____15715 =
          let uu____15716 =
            let uu____15727 =
              let uu____15728 =
                let uu____15733 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15733, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15728 in
            ([[l_or_a_b]], [aa; bb], uu____15727) in
          FStar_SMTEncoding_Util.mkForall uu____15716 in
        (uu____15715, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15708 in
    [uu____15707] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15796 =
      let uu____15797 =
        let uu____15804 =
          let uu____15805 =
            let uu____15816 =
              let uu____15817 =
                let uu____15822 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15822, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15817 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15816) in
          FStar_SMTEncoding_Util.mkForall uu____15805 in
        (uu____15804, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15797 in
    [uu____15796] in
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
    let uu____15895 =
      let uu____15896 =
        let uu____15903 =
          let uu____15904 =
            let uu____15915 =
              let uu____15916 =
                let uu____15921 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15921, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15916 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15915) in
          FStar_SMTEncoding_Util.mkForall uu____15904 in
        (uu____15903, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15896 in
    [uu____15895] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15992 =
      let uu____15993 =
        let uu____16000 =
          let uu____16001 =
            let uu____16012 =
              let uu____16013 =
                let uu____16018 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16018, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16013 in
            ([[l_imp_a_b]], [aa; bb], uu____16012) in
          FStar_SMTEncoding_Util.mkForall uu____16001 in
        (uu____16000, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15993 in
    [uu____15992] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16081 =
      let uu____16082 =
        let uu____16089 =
          let uu____16090 =
            let uu____16101 =
              let uu____16102 =
                let uu____16107 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16107, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16102 in
            ([[l_iff_a_b]], [aa; bb], uu____16101) in
          FStar_SMTEncoding_Util.mkForall uu____16090 in
        (uu____16089, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16082 in
    [uu____16081] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16159 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16159 in
    let uu____16162 =
      let uu____16163 =
        let uu____16170 =
          let uu____16171 =
            let uu____16182 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16182) in
          FStar_SMTEncoding_Util.mkForall uu____16171 in
        (uu____16170, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16163 in
    [uu____16162] in
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
      let uu____16242 =
        let uu____16249 =
          let uu____16252 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16252] in
        ("Valid", uu____16249) in
      FStar_SMTEncoding_Util.mkApp uu____16242 in
    let uu____16255 =
      let uu____16256 =
        let uu____16263 =
          let uu____16264 =
            let uu____16275 =
              let uu____16276 =
                let uu____16281 =
                  let uu____16282 =
                    let uu____16293 =
                      let uu____16298 =
                        let uu____16301 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16301] in
                      [uu____16298] in
                    let uu____16306 =
                      let uu____16307 =
                        let uu____16312 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16312, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16307 in
                    (uu____16293, [xx1], uu____16306) in
                  FStar_SMTEncoding_Util.mkForall uu____16282 in
                (uu____16281, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16276 in
            ([[l_forall_a_b]], [aa; bb], uu____16275) in
          FStar_SMTEncoding_Util.mkForall uu____16264 in
        (uu____16263, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16256 in
    [uu____16255] in
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
      let uu____16394 =
        let uu____16401 =
          let uu____16404 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16404] in
        ("Valid", uu____16401) in
      FStar_SMTEncoding_Util.mkApp uu____16394 in
    let uu____16407 =
      let uu____16408 =
        let uu____16415 =
          let uu____16416 =
            let uu____16427 =
              let uu____16428 =
                let uu____16433 =
                  let uu____16434 =
                    let uu____16445 =
                      let uu____16450 =
                        let uu____16453 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16453] in
                      [uu____16450] in
                    let uu____16458 =
                      let uu____16459 =
                        let uu____16464 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16464, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16459 in
                    (uu____16445, [xx1], uu____16458) in
                  FStar_SMTEncoding_Util.mkExists uu____16434 in
                (uu____16433, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16428 in
            ([[l_exists_a_b]], [aa; bb], uu____16427) in
          FStar_SMTEncoding_Util.mkForall uu____16416 in
        (uu____16415, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16408 in
    [uu____16407] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16524 =
      let uu____16525 =
        let uu____16532 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16533 = varops.mk_unique "typing_range_const" in
        (uu____16532, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16533) in
      FStar_SMTEncoding_Util.mkAssume uu____16525 in
    [uu____16524] in
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
        let uu____16567 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16567 x1 t in
      let uu____16568 =
        let uu____16579 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16579) in
      FStar_SMTEncoding_Util.mkForall uu____16568 in
    let uu____16602 =
      let uu____16603 =
        let uu____16610 =
          let uu____16611 =
            let uu____16622 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16622) in
          FStar_SMTEncoding_Util.mkForall uu____16611 in
        (uu____16610,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16603 in
    [uu____16602] in
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
          let uu____16946 =
            FStar_Util.find_opt
              (fun uu____16972  ->
                 match uu____16972 with
                 | (l,uu____16984) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16946 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17009,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17048 = encode_function_type_as_formula t env in
        match uu____17048 with
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
              let uu____17094 =
                ((let uu____17097 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17097) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17094
              then
                let uu____17104 = new_term_constant_and_tok_from_lid env lid in
                match uu____17104 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17123 =
                        let uu____17124 = FStar_Syntax_Subst.compress t_norm in
                        uu____17124.FStar_Syntax_Syntax.n in
                      match uu____17123 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17130) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17160  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17165 -> [] in
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
                (let uu____17179 = prims.is lid in
                 if uu____17179
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17187 = prims.mk lid vname in
                   match uu____17187 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17211 =
                      let uu____17222 = curried_arrow_formals_comp t_norm in
                      match uu____17222 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17240 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17240
                            then
                              let uu____17241 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___149_17244 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___149_17244.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___149_17244.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___149_17244.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___149_17244.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___149_17244.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___149_17244.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___149_17244.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___149_17244.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___149_17244.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___149_17244.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___149_17244.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___149_17244.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___149_17244.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___149_17244.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___149_17244.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___149_17244.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___149_17244.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___149_17244.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___149_17244.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___149_17244.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___149_17244.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___149_17244.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___149_17244.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___149_17244.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___149_17244.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___149_17244.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___149_17244.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___149_17244.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___149_17244.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17241
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17256 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17256)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17211 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17301 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17301 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17322 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___121_17364  ->
                                       match uu___121_17364 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17368 =
                                             FStar_Util.prefix vars in
                                           (match uu____17368 with
                                            | (uu____17389,(xxsym,uu____17391))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17409 =
                                                  let uu____17410 =
                                                    let uu____17417 =
                                                      let uu____17418 =
                                                        let uu____17429 =
                                                          let uu____17430 =
                                                            let uu____17435 =
                                                              let uu____17436
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17436 in
                                                            (vapp,
                                                              uu____17435) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17430 in
                                                        ([[vapp]], vars,
                                                          uu____17429) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17418 in
                                                    (uu____17417,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17410 in
                                                [uu____17409])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17455 =
                                             FStar_Util.prefix vars in
                                           (match uu____17455 with
                                            | (uu____17476,(xxsym,uu____17478))
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
                                                let uu____17501 =
                                                  let uu____17502 =
                                                    let uu____17509 =
                                                      let uu____17510 =
                                                        let uu____17521 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17521) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17510 in
                                                    (uu____17509,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17502 in
                                                [uu____17501])
                                       | uu____17538 -> [])) in
                             let uu____17539 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17539 with
                              | (vars,guards,env',decls1,uu____17566) ->
                                  let uu____17579 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17588 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17588, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17590 =
                                          encode_formula p env' in
                                        (match uu____17590 with
                                         | (g,ds) ->
                                             let uu____17601 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17601,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17579 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17614 =
                                           let uu____17621 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17621) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17614 in
                                       let uu____17630 =
                                         let vname_decl =
                                           let uu____17638 =
                                             let uu____17649 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17659  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17649,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17638 in
                                         let uu____17668 =
                                           let env2 =
                                             let uu___150_17674 = env1 in
                                             {
                                               bindings =
                                                 (uu___150_17674.bindings);
                                               depth = (uu___150_17674.depth);
                                               tcenv = (uu___150_17674.tcenv);
                                               warn = (uu___150_17674.warn);
                                               cache = (uu___150_17674.cache);
                                               nolabels =
                                                 (uu___150_17674.nolabels);
                                               use_zfuel_name =
                                                 (uu___150_17674.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___150_17674.current_module_name)
                                             } in
                                           let uu____17675 =
                                             let uu____17676 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17676 in
                                           if uu____17675
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17668 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17691::uu____17692 ->
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
                                                     let uu____17732 =
                                                       let uu____17743 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17743) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17732 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17770 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17773 =
                                               match formals with
                                               | [] ->
                                                   let uu____17790 =
                                                     let uu____17791 =
                                                       let uu____17794 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17794 in
                                                     push_free_var env1 lid
                                                       vname uu____17791 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17790)
                                               | uu____17799 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17806 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17806 in
                                                   let name_tok_corr =
                                                     let uu____17808 =
                                                       let uu____17815 =
                                                         let uu____17816 =
                                                           let uu____17827 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17827) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17816 in
                                                       (uu____17815,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17808 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17773 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17630 with
                                        | (decls2,env2) ->
                                            let uu____17870 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17878 =
                                                encode_term res_t1 env' in
                                              match uu____17878 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17891 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17891, decls) in
                                            (match uu____17870 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17902 =
                                                     let uu____17909 =
                                                       let uu____17910 =
                                                         let uu____17921 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17921) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17910 in
                                                     (uu____17909,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17902 in
                                                 let freshness =
                                                   let uu____17937 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17937
                                                   then
                                                     let uu____17942 =
                                                       let uu____17943 =
                                                         let uu____17954 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17965 =
                                                           varops.next_id () in
                                                         (vname, uu____17954,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17965) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17943 in
                                                     let uu____17968 =
                                                       let uu____17971 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17971] in
                                                     uu____17942 ::
                                                       uu____17968
                                                   else [] in
                                                 let g =
                                                   let uu____17976 =
                                                     let uu____17979 =
                                                       let uu____17982 =
                                                         let uu____17985 =
                                                           let uu____17988 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17988 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17985 in
                                                       FStar_List.append
                                                         decls3 uu____17982 in
                                                     FStar_List.append decls2
                                                       uu____17979 in
                                                   FStar_List.append decls11
                                                     uu____17976 in
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
          let uu____18023 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18023 with
          | FStar_Pervasives_Native.None  ->
              let uu____18060 = encode_free_var false env x t t_norm [] in
              (match uu____18060 with
               | (decls,env1) ->
                   let uu____18087 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18087 with
                    | (n1,x',uu____18114) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18135) ->
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
            let uu____18195 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18195 with
            | (decls,env1) ->
                let uu____18214 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18214
                then
                  let uu____18221 =
                    let uu____18224 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18224 in
                  (uu____18221, env1)
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
             (fun uu____18279  ->
                fun lb  ->
                  match uu____18279 with
                  | (decls,env1) ->
                      let uu____18299 =
                        let uu____18306 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18306
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18299 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18328 = FStar_Syntax_Util.head_and_args t in
    match uu____18328 with
    | (hd1,args) ->
        let uu____18365 =
          let uu____18366 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18366.FStar_Syntax_Syntax.n in
        (match uu____18365 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18370,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18389 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18414  ->
      fun quals  ->
        match uu____18414 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18490 = FStar_Util.first_N nbinders formals in
              match uu____18490 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18571  ->
                         fun uu____18572  ->
                           match (uu____18571, uu____18572) with
                           | ((formal,uu____18590),(binder,uu____18592)) ->
                               let uu____18601 =
                                 let uu____18608 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18608) in
                               FStar_Syntax_Syntax.NT uu____18601) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18616 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18647  ->
                              match uu____18647 with
                              | (x,i) ->
                                  let uu____18658 =
                                    let uu___151_18659 = x in
                                    let uu____18660 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___151_18659.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___151_18659.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18660
                                    } in
                                  (uu____18658, i))) in
                    FStar_All.pipe_right uu____18616
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18678 =
                      let uu____18679 = FStar_Syntax_Subst.compress body in
                      let uu____18680 =
                        let uu____18681 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18681 in
                      FStar_Syntax_Syntax.extend_app_n uu____18679
                        uu____18680 in
                    uu____18678 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18742 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18742
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___152_18745 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_18745.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_18745.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_18745.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_18745.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_18745.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_18745.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_18745.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_18745.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_18745.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_18745.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_18745.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_18745.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_18745.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_18745.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_18745.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_18745.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_18745.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_18745.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_18745.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___152_18745.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___152_18745.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_18745.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_18745.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_18745.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_18745.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___152_18745.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___152_18745.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___152_18745.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___152_18745.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18778 = FStar_Syntax_Util.abs_formals e in
                match uu____18778 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18842::uu____18843 ->
                         let uu____18858 =
                           let uu____18859 =
                             let uu____18862 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18862 in
                           uu____18859.FStar_Syntax_Syntax.n in
                         (match uu____18858 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18905 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18905 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18947 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18947
                                   then
                                     let uu____18982 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18982 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19076  ->
                                                   fun uu____19077  ->
                                                     match (uu____19076,
                                                             uu____19077)
                                                     with
                                                     | ((x,uu____19095),
                                                        (b,uu____19097)) ->
                                                         let uu____19106 =
                                                           let uu____19113 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19113) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19106)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19115 =
                                            let uu____19136 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19136) in
                                          (uu____19115, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19204 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19204 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19293) ->
                              let uu____19298 =
                                let uu____19319 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19319 in
                              (uu____19298, true)
                          | uu____19384 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____19386 ->
                              let uu____19387 =
                                let uu____19388 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19389 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19388
                                  uu____19389 in
                              failwith uu____19387)
                     | uu____19414 ->
                         let uu____19415 =
                           let uu____19416 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19416.FStar_Syntax_Syntax.n in
                         (match uu____19415 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19461 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19461 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19493 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19493 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19576 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19632 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19632
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19644 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19738  ->
                            fun lb  ->
                              match uu____19738 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19833 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19833
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19836 =
                                      let uu____19851 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19851
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19836 with
                                    | (tok,decl,env2) ->
                                        let uu____19897 =
                                          let uu____19910 =
                                            let uu____19921 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19921, tok) in
                                          uu____19910 :: toks in
                                        (uu____19897, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19644 with
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
                        | uu____20104 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20112 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20112 vars)
                            else
                              (let uu____20114 =
                                 let uu____20121 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20121) in
                               FStar_SMTEncoding_Util.mkApp uu____20114) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20203;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20205;
                             FStar_Syntax_Syntax.lbeff = uu____20206;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20269 =
                              let uu____20276 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20276 with
                              | (tcenv',uu____20294,e_t) ->
                                  let uu____20300 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20311 -> failwith "Impossible" in
                                  (match uu____20300 with
                                   | (e1,t_norm1) ->
                                       ((let uu___155_20327 = env2 in
                                         {
                                           bindings =
                                             (uu___155_20327.bindings);
                                           depth = (uu___155_20327.depth);
                                           tcenv = tcenv';
                                           warn = (uu___155_20327.warn);
                                           cache = (uu___155_20327.cache);
                                           nolabels =
                                             (uu___155_20327.nolabels);
                                           use_zfuel_name =
                                             (uu___155_20327.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___155_20327.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___155_20327.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20269 with
                             | (env',e1,t_norm1) ->
                                 let uu____20337 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20337 with
                                  | ((binders,body,uu____20358,uu____20359),curry)
                                      ->
                                      ((let uu____20370 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20370
                                        then
                                          let uu____20371 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20372 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20371 uu____20372
                                        else ());
                                       (let uu____20374 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20374 with
                                        | (vars,guards,env'1,binder_decls,uu____20401)
                                            ->
                                            let body1 =
                                              let uu____20415 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20415
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20418 =
                                              let uu____20427 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20427
                                              then
                                                let uu____20438 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20439 =
                                                  encode_formula body1 env'1 in
                                                (uu____20438, uu____20439)
                                              else
                                                (let uu____20449 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20449)) in
                                            (match uu____20418 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20472 =
                                                     let uu____20479 =
                                                       let uu____20480 =
                                                         let uu____20491 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20491) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20480 in
                                                     let uu____20502 =
                                                       let uu____20505 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20505 in
                                                     (uu____20479,
                                                       uu____20502,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20472 in
                                                 let uu____20508 =
                                                   let uu____20511 =
                                                     let uu____20514 =
                                                       let uu____20517 =
                                                         let uu____20520 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20520 in
                                                       FStar_List.append
                                                         decls2 uu____20517 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20514 in
                                                   FStar_List.append decls1
                                                     uu____20511 in
                                                 (uu____20508, env2))))))
                        | uu____20525 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20610 = varops.fresh "fuel" in
                          (uu____20610, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20613 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20701  ->
                                  fun uu____20702  ->
                                    match (uu____20701, uu____20702) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20850 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20850 in
                                        let gtok =
                                          let uu____20852 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20852 in
                                        let env4 =
                                          let uu____20854 =
                                            let uu____20857 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20857 in
                                          push_free_var env3 flid gtok
                                            uu____20854 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20613 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____21013 t_norm
                              uu____21015 =
                              match (uu____21013, uu____21015) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21059;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21060;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21088 =
                                    let uu____21095 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____21095 with
                                    | (tcenv',uu____21117,e_t) ->
                                        let uu____21123 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21134 ->
                                              failwith "Impossible" in
                                        (match uu____21123 with
                                         | (e1,t_norm1) ->
                                             ((let uu___156_21150 = env3 in
                                               {
                                                 bindings =
                                                   (uu___156_21150.bindings);
                                                 depth =
                                                   (uu___156_21150.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___156_21150.warn);
                                                 cache =
                                                   (uu___156_21150.cache);
                                                 nolabels =
                                                   (uu___156_21150.nolabels);
                                                 use_zfuel_name =
                                                   (uu___156_21150.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___156_21150.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___156_21150.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____21088 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21165 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21165
                                         then
                                           let uu____21166 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21167 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21168 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21166 uu____21167
                                             uu____21168
                                         else ());
                                        (let uu____21170 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21170 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21207 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21207
                                               then
                                                 let uu____21208 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21209 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21210 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21211 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21208 uu____21209
                                                   uu____21210 uu____21211
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21215 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21215 with
                                               | (vars,guards,env'1,binder_decls,uu____21246)
                                                   ->
                                                   let decl_g =
                                                     let uu____21260 =
                                                       let uu____21271 =
                                                         let uu____21274 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21274 in
                                                       (g, uu____21271,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21260 in
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
                                                     let uu____21299 =
                                                       let uu____21306 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21306) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21299 in
                                                   let gsapp =
                                                     let uu____21316 =
                                                       let uu____21323 =
                                                         let uu____21326 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21326 ::
                                                           vars_tm in
                                                       (g, uu____21323) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21316 in
                                                   let gmax =
                                                     let uu____21332 =
                                                       let uu____21339 =
                                                         let uu____21342 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21342 ::
                                                           vars_tm in
                                                       (g, uu____21339) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21332 in
                                                   let body1 =
                                                     let uu____21348 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21348
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21350 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21350 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21368 =
                                                            let uu____21375 =
                                                              let uu____21376
                                                                =
                                                                let uu____21391
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
                                                                  uu____21391) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21376 in
                                                            let uu____21412 =
                                                              let uu____21415
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21415 in
                                                            (uu____21375,
                                                              uu____21412,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21368 in
                                                        let eqn_f =
                                                          let uu____21419 =
                                                            let uu____21426 =
                                                              let uu____21427
                                                                =
                                                                let uu____21438
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21438) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21427 in
                                                            (uu____21426,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21419 in
                                                        let eqn_g' =
                                                          let uu____21452 =
                                                            let uu____21459 =
                                                              let uu____21460
                                                                =
                                                                let uu____21471
                                                                  =
                                                                  let uu____21472
                                                                    =
                                                                    let uu____21477
                                                                    =
                                                                    let uu____21478
                                                                    =
                                                                    let uu____21485
                                                                    =
                                                                    let uu____21488
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21488
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21485) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21478 in
                                                                    (gsapp,
                                                                    uu____21477) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21472 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21471) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21460 in
                                                            (uu____21459,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21452 in
                                                        let uu____21511 =
                                                          let uu____21520 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21520
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21549)
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
                                                                  let uu____21574
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21574
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21579
                                                                  =
                                                                  let uu____21586
                                                                    =
                                                                    let uu____21587
                                                                    =
                                                                    let uu____21598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21598) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21587 in
                                                                  (uu____21586,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21579 in
                                                              let uu____21619
                                                                =
                                                                let uu____21626
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21626
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21639
                                                                    =
                                                                    let uu____21642
                                                                    =
                                                                    let uu____21643
                                                                    =
                                                                    let uu____21650
                                                                    =
                                                                    let uu____21651
                                                                    =
                                                                    let uu____21662
                                                                    =
                                                                    let uu____21663
                                                                    =
                                                                    let uu____21668
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21668,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21663 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21662) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21651 in
                                                                    (uu____21650,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21643 in
                                                                    [uu____21642] in
                                                                    (d3,
                                                                    uu____21639) in
                                                              (match uu____21619
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21511
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
                            let uu____21733 =
                              let uu____21746 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21825  ->
                                   fun uu____21826  ->
                                     match (uu____21825, uu____21826) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21981 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21981 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21746 in
                            (match uu____21733 with
                             | (decls2,eqns,env01) ->
                                 let uu____22054 =
                                   let isDeclFun uu___122_22066 =
                                     match uu___122_22066 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22067 -> true
                                     | uu____22078 -> false in
                                   let uu____22079 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____22079
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____22054 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____22119 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___123_22123  ->
                                 match uu___123_22123 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22124 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22130 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22130))) in
                      if uu____22119
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
                   let uu____22182 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22182
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
        let uu____22231 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22231 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22235 = encode_sigelt' env se in
      match uu____22235 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22251 =
                  let uu____22252 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22252 in
                [uu____22251]
            | uu____22253 ->
                let uu____22254 =
                  let uu____22257 =
                    let uu____22258 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22258 in
                  uu____22257 :: g in
                let uu____22259 =
                  let uu____22262 =
                    let uu____22263 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22263 in
                  [uu____22262] in
                FStar_List.append uu____22254 uu____22259 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22276 =
          let uu____22277 = FStar_Syntax_Subst.compress t in
          uu____22277.FStar_Syntax_Syntax.n in
        match uu____22276 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22281)) -> s = "opaque_to_smt"
        | uu____22282 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22287 =
          let uu____22288 = FStar_Syntax_Subst.compress t in
          uu____22288.FStar_Syntax_Syntax.n in
        match uu____22287 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22292)) -> s = "uninterpreted_by_smt"
        | uu____22293 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22298 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22303 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22306 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22309 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22324 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22328 =
            let uu____22329 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22329 Prims.op_Negation in
          if uu____22328
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22355 ->
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
               let uu____22375 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22375 with
               | (aname,atok,env2) ->
                   let uu____22391 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22391 with
                    | (formals,uu____22409) ->
                        let uu____22422 =
                          let uu____22427 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22427 env2 in
                        (match uu____22422 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22439 =
                                 let uu____22440 =
                                   let uu____22451 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22467  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22451,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22440 in
                               [uu____22439;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22480 =
                               let aux uu____22532 uu____22533 =
                                 match (uu____22532, uu____22533) with
                                 | ((bv,uu____22585),(env3,acc_sorts,acc)) ->
                                     let uu____22623 = gen_term_var env3 bv in
                                     (match uu____22623 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22480 with
                              | (uu____22695,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22718 =
                                      let uu____22725 =
                                        let uu____22726 =
                                          let uu____22737 =
                                            let uu____22738 =
                                              let uu____22743 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22743) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22738 in
                                          ([[app]], xs_sorts, uu____22737) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22726 in
                                      (uu____22725,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22718 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22763 =
                                      let uu____22770 =
                                        let uu____22771 =
                                          let uu____22782 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22782) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22771 in
                                      (uu____22770,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22763 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22801 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22801 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22829,uu____22830)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22831 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22831 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22848,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22854 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___124_22858  ->
                      match uu___124_22858 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22859 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22864 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22865 -> false)) in
            Prims.op_Negation uu____22854 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22874 =
               let uu____22881 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22881 env fv t quals in
             match uu____22874 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22896 =
                   let uu____22899 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22899 in
                 (uu____22896, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22907 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22907 with
           | (uu____22916,f1) ->
               let uu____22918 = encode_formula f1 env in
               (match uu____22918 with
                | (f2,decls) ->
                    let g =
                      let uu____22932 =
                        let uu____22933 =
                          let uu____22940 =
                            let uu____22943 =
                              let uu____22944 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22944 in
                            FStar_Pervasives_Native.Some uu____22943 in
                          let uu____22945 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22940, uu____22945) in
                        FStar_SMTEncoding_Util.mkAssume uu____22933 in
                      [uu____22932] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22951) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22963 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22981 =
                       let uu____22984 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22984.FStar_Syntax_Syntax.fv_name in
                     uu____22981.FStar_Syntax_Syntax.v in
                   let uu____22985 =
                     let uu____22986 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22986 in
                   if uu____22985
                   then
                     let val_decl =
                       let uu___159_23014 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___159_23014.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___159_23014.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___159_23014.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23019 = encode_sigelt' env1 val_decl in
                     match uu____23019 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22963 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23047,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23049;
                          FStar_Syntax_Syntax.lbtyp = uu____23050;
                          FStar_Syntax_Syntax.lbeff = uu____23051;
                          FStar_Syntax_Syntax.lbdef = uu____23052;_}::[]),uu____23053)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23072 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23072 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23101 =
                   let uu____23104 =
                     let uu____23105 =
                       let uu____23112 =
                         let uu____23113 =
                           let uu____23124 =
                             let uu____23125 =
                               let uu____23130 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23130) in
                             FStar_SMTEncoding_Util.mkEq uu____23125 in
                           ([[b2t_x]], [xx], uu____23124) in
                         FStar_SMTEncoding_Util.mkForall uu____23113 in
                       (uu____23112,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23105 in
                   [uu____23104] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23101 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23163,uu____23164) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_23173  ->
                  match uu___125_23173 with
                  | FStar_Syntax_Syntax.Discriminator uu____23174 -> true
                  | uu____23175 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23178,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23189 =
                     let uu____23190 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23190.FStar_Ident.idText in
                   uu____23189 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___126_23194  ->
                     match uu___126_23194 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23195 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23199) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___127_23216  ->
                  match uu___127_23216 with
                  | FStar_Syntax_Syntax.Projector uu____23217 -> true
                  | uu____23222 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23225 = try_lookup_free_var env l in
          (match uu____23225 with
           | FStar_Pervasives_Native.Some uu____23232 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___160_23236 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___160_23236.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___160_23236.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___160_23236.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23243) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23261) ->
          let uu____23270 = encode_sigelts env ses in
          (match uu____23270 with
           | (g,env1) ->
               let uu____23287 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___128_23310  ->
                         match uu___128_23310 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23311;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23312;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23313;_}
                             -> false
                         | uu____23316 -> true)) in
               (match uu____23287 with
                | (g',inversions) ->
                    let uu____23331 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___129_23352  ->
                              match uu___129_23352 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23353 ->
                                  true
                              | uu____23364 -> false)) in
                    (match uu____23331 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23382,tps,k,uu____23385,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___130_23402  ->
                    match uu___130_23402 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23403 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23412 = c in
              match uu____23412 with
              | (name,args,uu____23417,uu____23418,uu____23419) ->
                  let uu____23424 =
                    let uu____23425 =
                      let uu____23436 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23453  ->
                                match uu____23453 with
                                | (uu____23460,sort,uu____23462) -> sort)) in
                      (name, uu____23436, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23425 in
                  [uu____23424]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23489 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23495 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23495 FStar_Option.isNone)) in
            if uu____23489
            then []
            else
              (let uu____23527 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23527 with
               | (xxsym,xx) ->
                   let uu____23536 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23575  ->
                             fun l  ->
                               match uu____23575 with
                               | (out,decls) ->
                                   let uu____23595 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23595 with
                                    | (uu____23606,data_t) ->
                                        let uu____23608 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23608 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23654 =
                                                 let uu____23655 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23655.FStar_Syntax_Syntax.n in
                                               match uu____23654 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23666,indices) ->
                                                   indices
                                               | uu____23688 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23712  ->
                                                         match uu____23712
                                                         with
                                                         | (x,uu____23718) ->
                                                             let uu____23719
                                                               =
                                                               let uu____23720
                                                                 =
                                                                 let uu____23727
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23727,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23720 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23719)
                                                    env) in
                                             let uu____23730 =
                                               encode_args indices env1 in
                                             (match uu____23730 with
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
                                                      let uu____23756 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23772
                                                                 =
                                                                 let uu____23777
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23777,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23772)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23756
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23780 =
                                                      let uu____23781 =
                                                        let uu____23786 =
                                                          let uu____23787 =
                                                            let uu____23792 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23792,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23787 in
                                                        (out, uu____23786) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23781 in
                                                    (uu____23780,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23536 with
                    | (data_ax,decls) ->
                        let uu____23805 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23805 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23816 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23816 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23820 =
                                 let uu____23827 =
                                   let uu____23828 =
                                     let uu____23839 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23854 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23839,
                                       uu____23854) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23828 in
                                 let uu____23869 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23827,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23869) in
                               FStar_SMTEncoding_Util.mkAssume uu____23820 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23872 =
            let uu____23885 =
              let uu____23886 = FStar_Syntax_Subst.compress k in
              uu____23886.FStar_Syntax_Syntax.n in
            match uu____23885 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23931 -> (tps, k) in
          (match uu____23872 with
           | (formals,res) ->
               let uu____23954 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23954 with
                | (formals1,res1) ->
                    let uu____23965 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23965 with
                     | (vars,guards,env',binder_decls,uu____23990) ->
                         let uu____24003 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____24003 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24022 =
                                  let uu____24029 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24029) in
                                FStar_SMTEncoding_Util.mkApp uu____24022 in
                              let uu____24038 =
                                let tname_decl =
                                  let uu____24048 =
                                    let uu____24049 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24081  ->
                                              match uu____24081 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24094 = varops.next_id () in
                                    (tname, uu____24049,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24094, false) in
                                  constructor_or_logic_type_decl uu____24048 in
                                let uu____24103 =
                                  match vars with
                                  | [] ->
                                      let uu____24116 =
                                        let uu____24117 =
                                          let uu____24120 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____24120 in
                                        push_free_var env1 t tname
                                          uu____24117 in
                                      ([], uu____24116)
                                  | uu____24127 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24136 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24136 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24150 =
                                          let uu____24157 =
                                            let uu____24158 =
                                              let uu____24173 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24173) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24158 in
                                          (uu____24157,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24150 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24103 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24038 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24213 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24213 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24231 =
                                               let uu____24232 =
                                                 let uu____24239 =
                                                   let uu____24240 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24240 in
                                                 (uu____24239,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24232 in
                                             [uu____24231]
                                           else [] in
                                         let uu____24244 =
                                           let uu____24247 =
                                             let uu____24250 =
                                               let uu____24251 =
                                                 let uu____24258 =
                                                   let uu____24259 =
                                                     let uu____24270 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24270) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24259 in
                                                 (uu____24258,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24251 in
                                             [uu____24250] in
                                           FStar_List.append karr uu____24247 in
                                         FStar_List.append decls1 uu____24244 in
                                   let aux =
                                     let uu____24286 =
                                       let uu____24289 =
                                         inversion_axioms tapp vars in
                                       let uu____24292 =
                                         let uu____24295 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24295] in
                                       FStar_List.append uu____24289
                                         uu____24292 in
                                     FStar_List.append kindingAx uu____24286 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24302,uu____24303,uu____24304,uu____24305,uu____24306)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24314,t,uu____24316,n_tps,uu____24318) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24326 = new_term_constant_and_tok_from_lid env d in
          (match uu____24326 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24343 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24343 with
                | (formals,t_res) ->
                    let uu____24378 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24378 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24392 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24392 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24462 =
                                            mk_term_projector_name d x in
                                          (uu____24462,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24464 =
                                  let uu____24483 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24483, true) in
                                FStar_All.pipe_right uu____24464
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
                              let uu____24522 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24522 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24534::uu____24535 ->
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
                                         let uu____24580 =
                                           let uu____24591 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24591) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24580
                                     | uu____24616 -> tok_typing in
                                   let uu____24625 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24625 with
                                    | (vars',guards',env'',decls_formals,uu____24650)
                                        ->
                                        let uu____24663 =
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
                                        (match uu____24663 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24694 ->
                                                   let uu____24701 =
                                                     let uu____24702 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24702 in
                                                   [uu____24701] in
                                             let encode_elim uu____24712 =
                                               let uu____24713 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24713 with
                                               | (head1,args) ->
                                                   let uu____24756 =
                                                     let uu____24757 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24757.FStar_Syntax_Syntax.n in
                                                   (match uu____24756 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24767;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24768;_},uu____24769)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24775 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24775
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
                                                                 | uu____24818
                                                                    ->
                                                                    let uu____24819
                                                                    =
                                                                    let uu____24820
                                                                    =
                                                                    let uu____24825
                                                                    =
                                                                    let uu____24826
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24826 in
                                                                    (uu____24825,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24820 in
                                                                    FStar_Exn.raise
                                                                    uu____24819 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24842
                                                                    =
                                                                    let uu____24843
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24843 in
                                                                    if
                                                                    uu____24842
                                                                    then
                                                                    let uu____24856
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24856]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24858
                                                               =
                                                               let uu____24871
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24921
                                                                     ->
                                                                    fun
                                                                    uu____24922
                                                                     ->
                                                                    match 
                                                                    (uu____24921,
                                                                    uu____24922)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25017
                                                                    =
                                                                    let uu____25024
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25024 in
                                                                    (match uu____25017
                                                                    with
                                                                    | 
                                                                    (uu____25037,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25045
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25045
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25047
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25047
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
                                                                 uu____24871 in
                                                             (match uu____24858
                                                              with
                                                              | (uu____25062,arg_vars,elim_eqns_or_guards,uu____25065)
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
                                                                    let uu____25095
                                                                    =
                                                                    let uu____25102
                                                                    =
                                                                    let uu____25103
                                                                    =
                                                                    let uu____25114
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25125
                                                                    =
                                                                    let uu____25126
                                                                    =
                                                                    let uu____25131
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25131) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25126 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25114,
                                                                    uu____25125) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25103 in
                                                                    (uu____25102,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25095 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25154
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25154,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25156
                                                                    =
                                                                    let uu____25163
                                                                    =
                                                                    let uu____25164
                                                                    =
                                                                    let uu____25175
                                                                    =
                                                                    let uu____25180
                                                                    =
                                                                    let uu____25183
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25183] in
                                                                    [uu____25180] in
                                                                    let uu____25188
                                                                    =
                                                                    let uu____25189
                                                                    =
                                                                    let uu____25194
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25195
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25194,
                                                                    uu____25195) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25189 in
                                                                    (uu____25175,
                                                                    [x],
                                                                    uu____25188) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25164 in
                                                                    let uu____25214
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25163,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25214) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25156
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25221
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
                                                                    (let uu____25249
                                                                    =
                                                                    let uu____25250
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25250
                                                                    dapp1 in
                                                                    [uu____25249]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25221
                                                                    FStar_List.flatten in
                                                                    let uu____25257
                                                                    =
                                                                    let uu____25264
                                                                    =
                                                                    let uu____25265
                                                                    =
                                                                    let uu____25276
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25287
                                                                    =
                                                                    let uu____25288
                                                                    =
                                                                    let uu____25293
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25293) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25288 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25276,
                                                                    uu____25287) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25265 in
                                                                    (uu____25264,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25257) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25314 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25314
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
                                                                 | uu____25357
                                                                    ->
                                                                    let uu____25358
                                                                    =
                                                                    let uu____25359
                                                                    =
                                                                    let uu____25364
                                                                    =
                                                                    let uu____25365
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25365 in
                                                                    (uu____25364,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25359 in
                                                                    FStar_Exn.raise
                                                                    uu____25358 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25381
                                                                    =
                                                                    let uu____25382
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25382 in
                                                                    if
                                                                    uu____25381
                                                                    then
                                                                    let uu____25395
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25395]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25397
                                                               =
                                                               let uu____25410
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25460
                                                                     ->
                                                                    fun
                                                                    uu____25461
                                                                     ->
                                                                    match 
                                                                    (uu____25460,
                                                                    uu____25461)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25556
                                                                    =
                                                                    let uu____25563
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25563 in
                                                                    (match uu____25556
                                                                    with
                                                                    | 
                                                                    (uu____25576,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25584
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25584
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25586
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25586
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
                                                                 uu____25410 in
                                                             (match uu____25397
                                                              with
                                                              | (uu____25601,arg_vars,elim_eqns_or_guards,uu____25604)
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
                                                                    let uu____25634
                                                                    =
                                                                    let uu____25641
                                                                    =
                                                                    let uu____25642
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25664
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    let uu____25670
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25670) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25665 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25653,
                                                                    uu____25664) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25642 in
                                                                    (uu____25641,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25634 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25693
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25693,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25695
                                                                    =
                                                                    let uu____25702
                                                                    =
                                                                    let uu____25703
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    let uu____25719
                                                                    =
                                                                    let uu____25722
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25722] in
                                                                    [uu____25719] in
                                                                    let uu____25727
                                                                    =
                                                                    let uu____25728
                                                                    =
                                                                    let uu____25733
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25733,
                                                                    uu____25734) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25728 in
                                                                    (uu____25714,
                                                                    [x],
                                                                    uu____25727) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25703 in
                                                                    let uu____25753
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25702,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25753) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25695
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25760
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
                                                                    (let uu____25788
                                                                    =
                                                                    let uu____25789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25789
                                                                    dapp1 in
                                                                    [uu____25788]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25760
                                                                    FStar_List.flatten in
                                                                    let uu____25796
                                                                    =
                                                                    let uu____25803
                                                                    =
                                                                    let uu____25804
                                                                    =
                                                                    let uu____25815
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25826
                                                                    =
                                                                    let uu____25827
                                                                    =
                                                                    let uu____25832
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25832) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25827 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25815,
                                                                    uu____25826) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25804 in
                                                                    (uu____25803,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25796) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25851 ->
                                                        ((let uu____25853 =
                                                            let uu____25854 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25855 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25854
                                                              uu____25855 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25853);
                                                         ([], []))) in
                                             let uu____25860 = encode_elim () in
                                             (match uu____25860 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25880 =
                                                      let uu____25883 =
                                                        let uu____25886 =
                                                          let uu____25889 =
                                                            let uu____25892 =
                                                              let uu____25893
                                                                =
                                                                let uu____25904
                                                                  =
                                                                  let uu____25907
                                                                    =
                                                                    let uu____25908
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25908 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25907 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25904) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25893 in
                                                            [uu____25892] in
                                                          let uu____25913 =
                                                            let uu____25916 =
                                                              let uu____25919
                                                                =
                                                                let uu____25922
                                                                  =
                                                                  let uu____25925
                                                                    =
                                                                    let uu____25928
                                                                    =
                                                                    let uu____25931
                                                                    =
                                                                    let uu____25932
                                                                    =
                                                                    let uu____25939
                                                                    =
                                                                    let uu____25940
                                                                    =
                                                                    let uu____25951
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25951) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25940 in
                                                                    (uu____25939,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25932 in
                                                                    let uu____25964
                                                                    =
                                                                    let uu____25967
                                                                    =
                                                                    let uu____25968
                                                                    =
                                                                    let uu____25975
                                                                    =
                                                                    let uu____25976
                                                                    =
                                                                    let uu____25987
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25998
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25987,
                                                                    uu____25998) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25976 in
                                                                    (uu____25975,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25968 in
                                                                    [uu____25967] in
                                                                    uu____25931
                                                                    ::
                                                                    uu____25964 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25928 in
                                                                  FStar_List.append
                                                                    uu____25925
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25922 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25919 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25916 in
                                                          FStar_List.append
                                                            uu____25889
                                                            uu____25913 in
                                                        FStar_List.append
                                                          decls3 uu____25886 in
                                                      FStar_List.append
                                                        decls2 uu____25883 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25880 in
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
           (fun uu____26044  ->
              fun se  ->
                match uu____26044 with
                | (g,env1) ->
                    let uu____26064 = encode_sigelt env1 se in
                    (match uu____26064 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26123 =
        match uu____26123 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26155 ->
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
                 ((let uu____26161 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26161
                   then
                     let uu____26162 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26163 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26164 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26162 uu____26163 uu____26164
                   else ());
                  (let uu____26166 = encode_term t1 env1 in
                   match uu____26166 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26182 =
                         let uu____26189 =
                           let uu____26190 =
                             let uu____26191 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26191
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26190 in
                         new_term_constant_from_string env1 x uu____26189 in
                       (match uu____26182 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26207 = FStar_Options.log_queries () in
                              if uu____26207
                              then
                                let uu____26210 =
                                  let uu____26211 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26212 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26213 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26211 uu____26212 uu____26213 in
                                FStar_Pervasives_Native.Some uu____26210
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26229,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26243 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26243 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26266,se,uu____26268) ->
                 let uu____26273 = encode_sigelt env1 se in
                 (match uu____26273 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26290,se) ->
                 let uu____26296 = encode_sigelt env1 se in
                 (match uu____26296 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26313 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26313 with | (uu____26336,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26351 'Auu____26352 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26352,'Auu____26351)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26420  ->
              match uu____26420 with
              | (l,uu____26432,uu____26433) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26479  ->
              match uu____26479 with
              | (l,uu____26493,uu____26494) ->
                  let uu____26503 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26504 =
                    let uu____26507 =
                      let uu____26508 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26508 in
                    [uu____26507] in
                  uu____26503 :: uu____26504)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26530 =
      let uu____26533 =
        let uu____26534 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26537 =
          let uu____26538 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26538 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26534;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26537
        } in
      [uu____26533] in
    FStar_ST.op_Colon_Equals last_env uu____26530
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26565 = FStar_ST.op_Bang last_env in
      match uu____26565 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26587 ->
          let uu___161_26590 = e in
          let uu____26591 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_26590.bindings);
            depth = (uu___161_26590.depth);
            tcenv;
            warn = (uu___161_26590.warn);
            cache = (uu___161_26590.cache);
            nolabels = (uu___161_26590.nolabels);
            use_zfuel_name = (uu___161_26590.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_26590.encode_non_total_function_typ);
            current_module_name = uu____26591
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26596 = FStar_ST.op_Bang last_env in
    match uu____26596 with
    | [] -> failwith "Empty env stack"
    | uu____26617::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26642  ->
    let uu____26643 = FStar_ST.op_Bang last_env in
    match uu____26643 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_26672 = hd1 in
          {
            bindings = (uu___162_26672.bindings);
            depth = (uu___162_26672.depth);
            tcenv = (uu___162_26672.tcenv);
            warn = (uu___162_26672.warn);
            cache = refs;
            nolabels = (uu___162_26672.nolabels);
            use_zfuel_name = (uu___162_26672.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_26672.encode_non_total_function_typ);
            current_module_name = (uu___162_26672.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26694  ->
    let uu____26695 = FStar_ST.op_Bang last_env in
    match uu____26695 with
    | [] -> failwith "Popping an empty stack"
    | uu____26716::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____26741  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____26745  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____26749  ->
    let uu____26750 = FStar_ST.op_Bang last_env in
    match uu____26750 with
    | hd1::uu____26772::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26794 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
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
        | (uu____26859::uu____26860,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___163_26868 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___163_26868.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___163_26868.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___163_26868.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26869 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26886 =
        let uu____26889 =
          let uu____26890 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26890 in
        let uu____26891 = open_fact_db_tags env in uu____26889 :: uu____26891 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26886
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
      let uu____26915 = encode_sigelt env se in
      match uu____26915 with
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
        let uu____26953 = FStar_Options.log_queries () in
        if uu____26953
        then
          let uu____26956 =
            let uu____26957 =
              let uu____26958 =
                let uu____26959 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26959 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26958 in
            FStar_SMTEncoding_Term.Caption uu____26957 in
          uu____26956 :: decls
        else decls in
      let env =
        let uu____26970 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26970 tcenv in
      let uu____26971 = encode_top_level_facts env se in
      match uu____26971 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26985 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26985))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26999 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26999
       then
         let uu____27000 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27000
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27035  ->
                 fun se  ->
                   match uu____27035 with
                   | (g,env2) ->
                       let uu____27055 = encode_top_level_facts env2 se in
                       (match uu____27055 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27078 =
         encode_signature
           (let uu___164_27087 = env in
            {
              bindings = (uu___164_27087.bindings);
              depth = (uu___164_27087.depth);
              tcenv = (uu___164_27087.tcenv);
              warn = false;
              cache = (uu___164_27087.cache);
              nolabels = (uu___164_27087.nolabels);
              use_zfuel_name = (uu___164_27087.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___164_27087.encode_non_total_function_typ);
              current_module_name = (uu___164_27087.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27078 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27104 = FStar_Options.log_queries () in
             if uu____27104
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___165_27112 = env1 in
               {
                 bindings = (uu___165_27112.bindings);
                 depth = (uu___165_27112.depth);
                 tcenv = (uu___165_27112.tcenv);
                 warn = true;
                 cache = (uu___165_27112.cache);
                 nolabels = (uu___165_27112.nolabels);
                 use_zfuel_name = (uu___165_27112.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___165_27112.encode_non_total_function_typ);
                 current_module_name = (uu___165_27112.current_module_name)
               });
            (let uu____27114 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27114
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
        (let uu____27169 =
           let uu____27170 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27170.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27169);
        (let env =
           let uu____27172 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27172 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27184 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27219 = aux rest in
                 (match uu____27219 with
                  | (out,rest1) ->
                      let t =
                        let uu____27249 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27249 with
                        | FStar_Pervasives_Native.Some uu____27254 ->
                            let uu____27255 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27255
                              x.FStar_Syntax_Syntax.sort
                        | uu____27256 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27260 =
                        let uu____27263 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___166_27266 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_27266.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_27266.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27263 :: out in
                      (uu____27260, rest1))
             | uu____27271 -> ([], bindings1) in
           let uu____27278 = aux bindings in
           match uu____27278 with
           | (closing,bindings1) ->
               let uu____27303 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27303, bindings1) in
         match uu____27184 with
         | (q1,bindings1) ->
             let uu____27326 =
               let uu____27331 =
                 FStar_List.filter
                   (fun uu___131_27336  ->
                      match uu___131_27336 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27337 ->
                          false
                      | uu____27344 -> true) bindings1 in
               encode_env_bindings env uu____27331 in
             (match uu____27326 with
              | (env_decls,env1) ->
                  ((let uu____27362 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27362
                    then
                      let uu____27363 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27363
                    else ());
                   (let uu____27365 = encode_formula q1 env1 in
                    match uu____27365 with
                    | (phi,qdecls) ->
                        let uu____27386 =
                          let uu____27391 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27391 phi in
                        (match uu____27386 with
                         | (labels,phi1) ->
                             let uu____27408 = encode_labels labels in
                             (match uu____27408 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27445 =
                                      let uu____27452 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27453 =
                                        varops.mk_unique "@query" in
                                      (uu____27452,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27453) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27445 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____27472 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27472 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27474 = encode_formula q env in
       match uu____27474 with
       | (f,uu____27480) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27482) -> true
             | uu____27487 -> false)))