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
        let uu____4277 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____4277
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4279) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____4295) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4298 =
          let uu____4299 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____4299 in
        failwith uu____4298
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4320 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4333 ->
            let uu____4340 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4340
        | uu____4341 ->
            if norm1
            then let uu____4342 = whnf env t1 in aux false uu____4342
            else
              (let uu____4344 =
                 let uu____4345 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4346 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4345 uu____4346 in
               failwith uu____4344) in
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
    | uu____4378 ->
        let uu____4379 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4379)
let is_arithmetic_primitive:
  'Auu____4396 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4396 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4416::uu____4417::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4421::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4424 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4446 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4462 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4469 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4469)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4508)::uu____4509::uu____4510::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4561)::uu____4562::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4599 -> false
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
        (let uu____4808 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4808
         then
           let uu____4809 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4809
         else ());
        (let uu____4811 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4895  ->
                   fun b  ->
                     match uu____4895 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4974 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4990 = gen_term_var env1 x in
                           match uu____4990 with
                           | (xxsym,xx,env') ->
                               let uu____5014 =
                                 let uu____5019 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____5019 env1 xx in
                               (match uu____5014 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4974 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4811 with
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
          let uu____5178 = encode_term t env in
          match uu____5178 with
          | (t1,decls) ->
              let uu____5189 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____5189, decls)
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
          let uu____5200 = encode_term t env in
          match uu____5200 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5215 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____5215, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5217 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____5217, decls))
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
        let uu____5223 = encode_args args_e env in
        match uu____5223 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5242 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5251 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5251 in
            let binary arg_tms1 =
              let uu____5264 =
                let uu____5265 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5265 in
              let uu____5266 =
                let uu____5267 =
                  let uu____5268 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5268 in
                FStar_SMTEncoding_Term.unboxInt uu____5267 in
              (uu____5264, uu____5266) in
            let mk_default uu____5274 =
              let uu____5275 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5275 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5326 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5326
              then
                let uu____5327 = let uu____5328 = mk_args ts in op uu____5328 in
                FStar_All.pipe_right uu____5327 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5357 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5357
              then
                let uu____5358 = binary ts in
                match uu____5358 with
                | (t1,t2) ->
                    let uu____5365 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5365
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5369 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5369
                 then
                   let uu____5370 = op (binary ts) in
                   FStar_All.pipe_right uu____5370
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
            let uu____5501 =
              let uu____5510 =
                FStar_List.tryFind
                  (fun uu____5532  ->
                     match uu____5532 with
                     | (l,uu____5542) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5510 FStar_Util.must in
            (match uu____5501 with
             | (uu____5581,op) ->
                 let uu____5591 = op arg_tms in (uu____5591, decls))
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
        let uu____5599 = FStar_List.hd args_e in
        match uu____5599 with
        | (tm_sz,uu____5607) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5617 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5617 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5625 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5625);
                   t_decls) in
            let uu____5626 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5646::(sz_arg,uu____5648)::uu____5649::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5698 =
                    let uu____5701 = FStar_List.tail args_e in
                    FStar_List.tail uu____5701 in
                  let uu____5704 =
                    let uu____5707 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5707 in
                  (uu____5698, uu____5704)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5713::(sz_arg,uu____5715)::uu____5716::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5765 =
                    let uu____5766 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5766 in
                  failwith uu____5765
              | uu____5775 ->
                  let uu____5782 = FStar_List.tail args_e in
                  (uu____5782, FStar_Pervasives_Native.None) in
            (match uu____5626 with
             | (arg_tms,ext_sz) ->
                 let uu____5805 = encode_args arg_tms env in
                 (match uu____5805 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5826 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5835 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5835 in
                      let unary_arith arg_tms2 =
                        let uu____5844 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5844 in
                      let binary arg_tms2 =
                        let uu____5857 =
                          let uu____5858 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5858 in
                        let uu____5859 =
                          let uu____5860 =
                            let uu____5861 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5861 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5860 in
                        (uu____5857, uu____5859) in
                      let binary_arith arg_tms2 =
                        let uu____5876 =
                          let uu____5877 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5877 in
                        let uu____5878 =
                          let uu____5879 =
                            let uu____5880 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5880 in
                          FStar_SMTEncoding_Term.unboxInt uu____5879 in
                        (uu____5876, uu____5878) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5929 =
                          let uu____5930 = mk_args ts in op uu____5930 in
                        FStar_All.pipe_right uu____5929 resBox in
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
                        let uu____6020 =
                          let uu____6023 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____6023 in
                        let uu____6025 =
                          let uu____6028 =
                            let uu____6029 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____6029 in
                          FStar_SMTEncoding_Term.boxBitVec uu____6028 in
                        mk_bv uu____6020 unary uu____6025 arg_tms2 in
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
                      let uu____6204 =
                        let uu____6213 =
                          FStar_List.tryFind
                            (fun uu____6235  ->
                               match uu____6235 with
                               | (l,uu____6245) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6213 FStar_Util.must in
                      (match uu____6204 with
                       | (uu____6286,op) ->
                           let uu____6296 = op arg_tms1 in
                           (uu____6296, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6307 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6307
       then
         let uu____6308 = FStar_Syntax_Print.tag_of_term t in
         let uu____6309 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6310 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6308 uu____6309
           uu____6310
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6316 ->
           let uu____6341 =
             let uu____6342 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6343 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6344 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6345 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6342
               uu____6343 uu____6344 uu____6345 in
           failwith uu____6341
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6350 =
             let uu____6351 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6352 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6353 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6354 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6351
               uu____6352 uu____6353 uu____6354 in
           failwith uu____6350
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6360 =
             let uu____6361 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6361 in
           failwith uu____6360
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6368) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6410) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6420 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6420, [])
       | FStar_Syntax_Syntax.Tm_type uu____6423 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6427) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6433 = encode_const c in (uu____6433, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6455 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6455 with
            | (binders1,res) ->
                let uu____6466 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6466
                then
                  let uu____6471 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6471 with
                   | (vars,guards,env',decls,uu____6496) ->
                       let fsym =
                         let uu____6514 = varops.fresh "f" in
                         (uu____6514, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6517 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_6526 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_6526.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_6526.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_6526.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_6526.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_6526.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_6526.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_6526.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_6526.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_6526.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_6526.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_6526.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_6526.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_6526.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_6526.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_6526.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_6526.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_6526.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_6526.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_6526.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___141_6526.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___141_6526.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_6526.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_6526.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_6526.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_6526.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___141_6526.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___141_6526.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___141_6526.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___141_6526.FStar_TypeChecker_Env.identifier_info)
                            }) res in
                       (match uu____6517 with
                        | (pre_opt,res_t) ->
                            let uu____6537 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6537 with
                             | (res_pred,decls') ->
                                 let uu____6548 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6561 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6561, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6565 =
                                         encode_formula pre env' in
                                       (match uu____6565 with
                                        | (guard,decls0) ->
                                            let uu____6578 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6578, decls0)) in
                                 (match uu____6548 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6590 =
                                          let uu____6601 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6601) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6590 in
                                      let cvars =
                                        let uu____6619 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6619
                                          (FStar_List.filter
                                             (fun uu____6633  ->
                                                match uu____6633 with
                                                | (x,uu____6639) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6658 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6658 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6666 =
                                             let uu____6667 =
                                               let uu____6674 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6674) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6667 in
                                           (uu____6666,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6694 =
                                               let uu____6695 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6695 in
                                             varops.mk_unique uu____6694 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6706 =
                                               FStar_Options.log_queries () in
                                             if uu____6706
                                             then
                                               let uu____6709 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6709
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6717 =
                                               let uu____6724 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6724) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6717 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6736 =
                                               let uu____6743 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6743,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6736 in
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
                                             let uu____6764 =
                                               let uu____6771 =
                                                 let uu____6772 =
                                                   let uu____6783 =
                                                     let uu____6784 =
                                                       let uu____6789 =
                                                         let uu____6790 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6790 in
                                                       (f_has_t, uu____6789) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6784 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6783) in
                                                 mkForall_fuel uu____6772 in
                                               (uu____6771,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6764 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6813 =
                                               let uu____6820 =
                                                 let uu____6821 =
                                                   let uu____6832 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6832) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6821 in
                                               (uu____6820,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6813 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6857 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6857);
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
                     let uu____6872 =
                       let uu____6879 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6879,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6872 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6891 =
                       let uu____6898 =
                         let uu____6899 =
                           let uu____6910 =
                             let uu____6911 =
                               let uu____6916 =
                                 let uu____6917 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6917 in
                               (f_has_t, uu____6916) in
                             FStar_SMTEncoding_Util.mkImp uu____6911 in
                           ([[f_has_t]], [fsym], uu____6910) in
                         mkForall_fuel uu____6899 in
                       (uu____6898, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6891 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6944 ->
           let uu____6951 =
             let uu____6956 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6956 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6963;
                 FStar_Syntax_Syntax.vars = uu____6964;_} ->
                 let uu____6971 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6971 with
                  | (b,f1) ->
                      let uu____6996 =
                        let uu____6997 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6997 in
                      (uu____6996, f1))
             | uu____7006 -> failwith "impossible" in
           (match uu____6951 with
            | (x,f) ->
                let uu____7017 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____7017 with
                 | (base_t,decls) ->
                     let uu____7028 = gen_term_var env x in
                     (match uu____7028 with
                      | (x1,xtm,env') ->
                          let uu____7042 = encode_formula f env' in
                          (match uu____7042 with
                           | (refinement,decls') ->
                               let uu____7053 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____7053 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____7069 =
                                        let uu____7072 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____7079 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____7072
                                          uu____7079 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7069 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7112  ->
                                              match uu____7112 with
                                              | (y,uu____7118) ->
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
                                    let uu____7151 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7151 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7159 =
                                           let uu____7160 =
                                             let uu____7167 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7167) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7160 in
                                         (uu____7159,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7188 =
                                             let uu____7189 =
                                               let uu____7190 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7190 in
                                             Prims.strcat module_name
                                               uu____7189 in
                                           varops.mk_unique uu____7188 in
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
                                           let uu____7204 =
                                             let uu____7211 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7211) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7204 in
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
                                           let uu____7226 =
                                             let uu____7233 =
                                               let uu____7234 =
                                                 let uu____7245 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7245) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7234 in
                                             (uu____7233,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7226 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7271 =
                                             let uu____7278 =
                                               let uu____7279 =
                                                 let uu____7290 =
                                                   let uu____7291 =
                                                     let uu____7296 =
                                                       let uu____7297 =
                                                         let uu____7308 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7308) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7297 in
                                                     (uu____7296, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7291 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7290) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7279 in
                                             (uu____7278,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7271 in
                                         let t_kinding =
                                           let uu____7346 =
                                             let uu____7353 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7353,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7346 in
                                         let t_interp =
                                           let uu____7371 =
                                             let uu____7378 =
                                               let uu____7379 =
                                                 let uu____7390 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7390) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7379 in
                                             let uu____7413 =
                                               let uu____7416 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7416 in
                                             (uu____7378, uu____7413,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7371 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7423 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7423);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7453 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7453 in
           let uu____7454 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7454 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7466 =
                    let uu____7473 =
                      let uu____7474 =
                        let uu____7475 =
                          let uu____7476 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7476 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7475 in
                      varops.mk_unique uu____7474 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7473) in
                  FStar_SMTEncoding_Util.mkAssume uu____7466 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7481 ->
           let uu____7496 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7496 with
            | (head1,args_e) ->
                let uu____7537 =
                  let uu____7550 =
                    let uu____7551 = FStar_Syntax_Subst.compress head1 in
                    uu____7551.FStar_Syntax_Syntax.n in
                  (uu____7550, args_e) in
                (match uu____7537 with
                 | uu____7566 when head_redex env head1 ->
                     let uu____7579 = whnf env t in
                     encode_term uu____7579 env
                 | uu____7580 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7599 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7613;
                       FStar_Syntax_Syntax.vars = uu____7614;_},uu____7615),uu____7616::
                    (v1,uu____7618)::(v2,uu____7620)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7671 = encode_term v1 env in
                     (match uu____7671 with
                      | (v11,decls1) ->
                          let uu____7682 = encode_term v2 env in
                          (match uu____7682 with
                           | (v21,decls2) ->
                               let uu____7693 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7693,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7697::(v1,uu____7699)::(v2,uu____7701)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7748 = encode_term v1 env in
                     (match uu____7748 with
                      | (v11,decls1) ->
                          let uu____7759 = encode_term v2 env in
                          (match uu____7759 with
                           | (v21,decls2) ->
                               let uu____7770 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7770,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7773) ->
                     let e0 =
                       let uu____7791 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7791 in
                     ((let uu____7799 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7799
                       then
                         let uu____7800 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7800
                       else ());
                      (let e =
                         let uu____7805 =
                           let uu____7806 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7807 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7806
                             uu____7807 in
                         uu____7805 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7816),(arg,uu____7818)::[]) -> encode_term arg env
                 | uu____7843 ->
                     let uu____7856 = encode_args args_e env in
                     (match uu____7856 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7911 = encode_term head1 env in
                            match uu____7911 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7975 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7975 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8053  ->
                                                 fun uu____8054  ->
                                                   match (uu____8053,
                                                           uu____8054)
                                                   with
                                                   | ((bv,uu____8076),
                                                      (a,uu____8078)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____8096 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____8096
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____8101 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____8101 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____8116 =
                                                   let uu____8123 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____8132 =
                                                     let uu____8133 =
                                                       let uu____8134 =
                                                         let uu____8135 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____8135 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8134 in
                                                     varops.mk_unique
                                                       uu____8133 in
                                                   (uu____8123,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8132) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8116 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8152 = lookup_free_var_sym env fv in
                            match uu____8152 with
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
                                   FStar_Syntax_Syntax.pos = uu____8183;
                                   FStar_Syntax_Syntax.vars = uu____8184;_},uu____8185)
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
                                   FStar_Syntax_Syntax.pos = uu____8196;
                                   FStar_Syntax_Syntax.vars = uu____8197;_},uu____8198)
                                ->
                                let uu____8203 =
                                  let uu____8204 =
                                    let uu____8209 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8209
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8204
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8203
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8239 =
                                  let uu____8240 =
                                    let uu____8245 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8245
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8240
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8239
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8274,(FStar_Util.Inl t1,uu____8276),uu____8277)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8326,(FStar_Util.Inr c,uu____8328),uu____8329)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8378 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8405 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8405 in
                               let uu____8406 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8406 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8422;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8423;_},uu____8424)
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
                                     | uu____8438 ->
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
           let uu____8487 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8487 with
            | (bs1,body1,opening) ->
                let fallback uu____8510 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8517 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8517, [decl]) in
                let is_impure rc =
                  let uu____8524 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8524 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8534 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8534
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8554 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8554
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8558 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8558)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8565 =
                         let uu____8566 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8566 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8565);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8568 =
                       (is_impure rc) &&
                         (let uu____8570 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8570) in
                     if uu____8568
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8577 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8577 with
                        | (vars,guards,envbody,decls,uu____8602) ->
                            let body2 =
                              let uu____8616 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8616
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8618 = encode_term body2 envbody in
                            (match uu____8618 with
                             | (body3,decls') ->
                                 let uu____8629 =
                                   let uu____8638 = codomain_eff rc in
                                   match uu____8638 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8657 = encode_term tfun env in
                                       (match uu____8657 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8629 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8689 =
                                          let uu____8700 =
                                            let uu____8701 =
                                              let uu____8706 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8706, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8701 in
                                          ([], vars, uu____8700) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8689 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8718 =
                                              let uu____8721 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8721
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8718 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8740 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8740 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8748 =
                                             let uu____8749 =
                                               let uu____8756 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8756) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8749 in
                                           (uu____8748,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8767 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8767 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8778 =
                                                    let uu____8779 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8779 = cache_size in
                                                  if uu____8778
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
                                                    let uu____8795 =
                                                      let uu____8796 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8796 in
                                                    varops.mk_unique
                                                      uu____8795 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8803 =
                                                    let uu____8810 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8810) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8803 in
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
                                                      let uu____8828 =
                                                        let uu____8829 =
                                                          let uu____8836 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8836,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8829 in
                                                      [uu____8828] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8849 =
                                                    let uu____8856 =
                                                      let uu____8857 =
                                                        let uu____8868 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8868) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8857 in
                                                    (uu____8856,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8849 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8885 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8885);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8888,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8889;
                          FStar_Syntax_Syntax.lbunivs = uu____8890;
                          FStar_Syntax_Syntax.lbtyp = uu____8891;
                          FStar_Syntax_Syntax.lbeff = uu____8892;
                          FStar_Syntax_Syntax.lbdef = uu____8893;_}::uu____8894),uu____8895)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8921;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8923;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8944 ->
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
              let uu____9014 = encode_term e1 env in
              match uu____9014 with
              | (ee1,decls1) ->
                  let uu____9025 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9025 with
                   | (xs,e21) ->
                       let uu____9050 = FStar_List.hd xs in
                       (match uu____9050 with
                        | (x1,uu____9064) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9066 = encode_body e21 env' in
                            (match uu____9066 with
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
            let uu____9098 =
              let uu____9105 =
                let uu____9106 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9106 in
              gen_term_var env uu____9105 in
            match uu____9098 with
            | (scrsym,scr',env1) ->
                let uu____9114 = encode_term e env1 in
                (match uu____9114 with
                 | (scr,decls) ->
                     let uu____9125 =
                       let encode_branch b uu____9150 =
                         match uu____9150 with
                         | (else_case,decls1) ->
                             let uu____9169 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9169 with
                              | (p,w,br) ->
                                  let uu____9195 = encode_pat env1 p in
                                  (match uu____9195 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9232  ->
                                                   match uu____9232 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9239 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9261 =
                                               encode_term w1 env2 in
                                             (match uu____9261 with
                                              | (w2,decls2) ->
                                                  let uu____9274 =
                                                    let uu____9275 =
                                                      let uu____9280 =
                                                        let uu____9281 =
                                                          let uu____9286 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9286) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9281 in
                                                      (guard, uu____9280) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9275 in
                                                  (uu____9274, decls2)) in
                                       (match uu____9239 with
                                        | (guard1,decls2) ->
                                            let uu____9299 =
                                              encode_br br env2 in
                                            (match uu____9299 with
                                             | (br1,decls3) ->
                                                 let uu____9312 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9312,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9125 with
                      | (match_tm,decls1) ->
                          let uu____9331 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9331, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9371 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9371
       then
         let uu____9372 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9372
       else ());
      (let uu____9374 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9374 with
       | (vars,pat_term) ->
           let uu____9391 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9444  ->
                     fun v1  ->
                       match uu____9444 with
                       | (env1,vars1) ->
                           let uu____9496 = gen_term_var env1 v1 in
                           (match uu____9496 with
                            | (xx,uu____9518,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9391 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9597 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9598 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9599 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9607 =
                        let uu____9612 = encode_const c in
                        (scrutinee, uu____9612) in
                      FStar_SMTEncoding_Util.mkEq uu____9607
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9633 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9633 with
                        | (uu____9640,uu____9641::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9644 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9677  ->
                                  match uu____9677 with
                                  | (arg,uu____9685) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9691 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9691)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9718) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9749 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9772 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9816  ->
                                  match uu____9816 with
                                  | (arg,uu____9830) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9836 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9836)) in
                      FStar_All.pipe_right uu____9772 FStar_List.flatten in
                let pat_term1 uu____9864 = encode_term pat_term env1 in
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
      let uu____9874 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9912  ->
                fun uu____9913  ->
                  match (uu____9912, uu____9913) with
                  | ((tms,decls),(t,uu____9949)) ->
                      let uu____9970 = encode_term t env in
                      (match uu____9970 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9874 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10027 = FStar_Syntax_Util.list_elements e in
        match uu____10027 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____10048 =
          let uu____10063 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10063 FStar_Syntax_Util.head_and_args in
        match uu____10048 with
        | (head1,args) ->
            let uu____10102 =
              let uu____10115 =
                let uu____10116 = FStar_Syntax_Util.un_uinst head1 in
                uu____10116.FStar_Syntax_Syntax.n in
              (uu____10115, args) in
            (match uu____10102 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10130,uu____10131)::(e,uu____10133)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10168 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10204 =
            let uu____10219 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10219 FStar_Syntax_Util.head_and_args in
          match uu____10204 with
          | (head1,args) ->
              let uu____10260 =
                let uu____10273 =
                  let uu____10274 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10274.FStar_Syntax_Syntax.n in
                (uu____10273, args) in
              (match uu____10260 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10291)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10318 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10340 = smt_pat_or1 t1 in
            (match uu____10340 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10356 = list_elements1 e in
                 FStar_All.pipe_right uu____10356
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10374 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10374
                           (FStar_List.map one_pat)))
             | uu____10385 ->
                 let uu____10390 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10390])
        | uu____10411 ->
            let uu____10414 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10414] in
      let uu____10435 =
        let uu____10454 =
          let uu____10455 = FStar_Syntax_Subst.compress t in
          uu____10455.FStar_Syntax_Syntax.n in
        match uu____10454 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10494 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10494 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10537;
                        FStar_Syntax_Syntax.effect_name = uu____10538;
                        FStar_Syntax_Syntax.result_typ = uu____10539;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10541)::(post,uu____10543)::(pats,uu____10545)::[];
                        FStar_Syntax_Syntax.flags = uu____10546;_}
                      ->
                      let uu____10587 = lemma_pats pats in
                      (binders1, pre, post, uu____10587)
                  | uu____10604 -> failwith "impos"))
        | uu____10623 -> failwith "Impos" in
      match uu____10435 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___142_10671 = env in
            {
              bindings = (uu___142_10671.bindings);
              depth = (uu___142_10671.depth);
              tcenv = (uu___142_10671.tcenv);
              warn = (uu___142_10671.warn);
              cache = (uu___142_10671.cache);
              nolabels = (uu___142_10671.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___142_10671.encode_non_total_function_typ);
              current_module_name = (uu___142_10671.current_module_name)
            } in
          let uu____10672 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10672 with
           | (vars,guards,env2,decls,uu____10697) ->
               let uu____10710 =
                 let uu____10723 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10767 =
                             let uu____10776 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10776
                               FStar_List.unzip in
                           match uu____10767 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10723 FStar_List.unzip in
               (match uu____10710 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___143_10885 = env2 in
                      {
                        bindings = (uu___143_10885.bindings);
                        depth = (uu___143_10885.depth);
                        tcenv = (uu___143_10885.tcenv);
                        warn = (uu___143_10885.warn);
                        cache = (uu___143_10885.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___143_10885.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___143_10885.encode_non_total_function_typ);
                        current_module_name =
                          (uu___143_10885.current_module_name)
                      } in
                    let uu____10886 =
                      let uu____10891 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10891 env3 in
                    (match uu____10886 with
                     | (pre1,decls'') ->
                         let uu____10898 =
                           let uu____10903 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10903 env3 in
                         (match uu____10898 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10913 =
                                let uu____10914 =
                                  let uu____10925 =
                                    let uu____10926 =
                                      let uu____10931 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10931, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10926 in
                                  (pats, vars, uu____10925) in
                                FStar_SMTEncoding_Util.mkForall uu____10914 in
                              (uu____10913, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10950 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10950
        then
          let uu____10951 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10952 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10951 uu____10952
        else () in
      let enc f r l =
        let uu____10985 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11013 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11013 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10985 with
        | (decls,args) ->
            let uu____11042 =
              let uu___144_11043 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_11043.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_11043.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11042, decls) in
      let const_op f r uu____11074 =
        let uu____11087 = f r in (uu____11087, []) in
      let un_op f l =
        let uu____11106 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11106 in
      let bin_op f uu___118_11122 =
        match uu___118_11122 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11133 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11167 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11190  ->
                 match uu____11190 with
                 | (t,uu____11204) ->
                     let uu____11205 = encode_formula t env in
                     (match uu____11205 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11167 with
        | (decls,phis) ->
            let uu____11234 =
              let uu___145_11235 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_11235.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_11235.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11234, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11296  ->
               match uu____11296 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11315) -> false
                    | uu____11316 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11331 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11331
        else
          (let uu____11345 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11345 r rf) in
      let mk_imp1 r uu___119_11370 =
        match uu___119_11370 with
        | (lhs,uu____11376)::(rhs,uu____11378)::[] ->
            let uu____11405 = encode_formula rhs env in
            (match uu____11405 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11420) ->
                      (l1, decls1)
                  | uu____11425 ->
                      let uu____11426 = encode_formula lhs env in
                      (match uu____11426 with
                       | (l2,decls2) ->
                           let uu____11437 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11437, (FStar_List.append decls1 decls2)))))
        | uu____11440 -> failwith "impossible" in
      let mk_ite r uu___120_11461 =
        match uu___120_11461 with
        | (guard,uu____11467)::(_then,uu____11469)::(_else,uu____11471)::[]
            ->
            let uu____11508 = encode_formula guard env in
            (match uu____11508 with
             | (g,decls1) ->
                 let uu____11519 = encode_formula _then env in
                 (match uu____11519 with
                  | (t,decls2) ->
                      let uu____11530 = encode_formula _else env in
                      (match uu____11530 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11544 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11569 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11569 in
      let connectives =
        let uu____11587 =
          let uu____11600 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11600) in
        let uu____11617 =
          let uu____11632 =
            let uu____11645 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11645) in
          let uu____11662 =
            let uu____11677 =
              let uu____11692 =
                let uu____11705 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11705) in
              let uu____11722 =
                let uu____11737 =
                  let uu____11752 =
                    let uu____11765 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11765) in
                  [uu____11752;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11737 in
              uu____11692 :: uu____11722 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11677 in
          uu____11632 :: uu____11662 in
        uu____11587 :: uu____11617 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12086 = encode_formula phi' env in
            (match uu____12086 with
             | (phi2,decls) ->
                 let uu____12097 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12097, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12098 ->
            let uu____12105 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12105 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12144 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12144 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12156;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12158;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12179 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12179 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12226::(x,uu____12228)::(t,uu____12230)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12277 = encode_term x env in
                 (match uu____12277 with
                  | (x1,decls) ->
                      let uu____12288 = encode_term t env in
                      (match uu____12288 with
                       | (t1,decls') ->
                           let uu____12299 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12299, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12304)::(msg,uu____12306)::(phi2,uu____12308)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12353 =
                   let uu____12358 =
                     let uu____12359 = FStar_Syntax_Subst.compress r in
                     uu____12359.FStar_Syntax_Syntax.n in
                   let uu____12362 =
                     let uu____12363 = FStar_Syntax_Subst.compress msg in
                     uu____12363.FStar_Syntax_Syntax.n in
                   (uu____12358, uu____12362) in
                 (match uu____12353 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12372))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12378 -> fallback phi2)
             | uu____12383 when head_redex env head2 ->
                 let uu____12396 = whnf env phi1 in
                 encode_formula uu____12396 env
             | uu____12397 ->
                 let uu____12410 = encode_term phi1 env in
                 (match uu____12410 with
                  | (tt,decls) ->
                      let uu____12421 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___146_12424 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___146_12424.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___146_12424.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12421, decls)))
        | uu____12425 ->
            let uu____12426 = encode_term phi1 env in
            (match uu____12426 with
             | (tt,decls) ->
                 let uu____12437 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___147_12440 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___147_12440.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___147_12440.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12437, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12476 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12476 with
        | (vars,guards,env2,decls,uu____12515) ->
            let uu____12528 =
              let uu____12541 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12589 =
                          let uu____12598 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12628  ->
                                    match uu____12628 with
                                    | (t,uu____12638) ->
                                        encode_term t
                                          (let uu___148_12640 = env2 in
                                           {
                                             bindings =
                                               (uu___148_12640.bindings);
                                             depth = (uu___148_12640.depth);
                                             tcenv = (uu___148_12640.tcenv);
                                             warn = (uu___148_12640.warn);
                                             cache = (uu___148_12640.cache);
                                             nolabels =
                                               (uu___148_12640.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___148_12640.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___148_12640.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12598 FStar_List.unzip in
                        match uu____12589 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12541 FStar_List.unzip in
            (match uu____12528 with
             | (pats,decls') ->
                 let uu____12739 = encode_formula body env2 in
                 (match uu____12739 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12771;
                             FStar_SMTEncoding_Term.rng = uu____12772;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12787 -> guards in
                      let uu____12792 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12792, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12852  ->
                   match uu____12852 with
                   | (x,uu____12858) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12866 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12878 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12878) uu____12866 tl1 in
             let uu____12881 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12908  ->
                       match uu____12908 with
                       | (b,uu____12914) ->
                           let uu____12915 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12915)) in
             (match uu____12881 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12921) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12935 =
                    let uu____12936 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12936 in
                  FStar_Errors.warn pos uu____12935) in
       let uu____12937 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12937 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12946 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13004  ->
                     match uu____13004 with
                     | (l,uu____13018) -> FStar_Ident.lid_equals op l)) in
           (match uu____12946 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13051,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13091 = encode_q_body env vars pats body in
             match uu____13091 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13136 =
                     let uu____13147 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13147) in
                   FStar_SMTEncoding_Term.mkForall uu____13136
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13166 = encode_q_body env vars pats body in
             match uu____13166 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13210 =
                   let uu____13211 =
                     let uu____13222 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13222) in
                   FStar_SMTEncoding_Term.mkExists uu____13211
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13210, decls))))
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
  let uu____13320 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13320 with
  | (asym,a) ->
      let uu____13327 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13327 with
       | (xsym,x) ->
           let uu____13334 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13334 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13378 =
                      let uu____13389 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13389, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13378 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13415 =
                      let uu____13422 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13422) in
                    FStar_SMTEncoding_Util.mkApp uu____13415 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13435 =
                    let uu____13438 =
                      let uu____13441 =
                        let uu____13444 =
                          let uu____13445 =
                            let uu____13452 =
                              let uu____13453 =
                                let uu____13464 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13464) in
                              FStar_SMTEncoding_Util.mkForall uu____13453 in
                            (uu____13452, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13445 in
                        let uu____13481 =
                          let uu____13484 =
                            let uu____13485 =
                              let uu____13492 =
                                let uu____13493 =
                                  let uu____13504 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13504) in
                                FStar_SMTEncoding_Util.mkForall uu____13493 in
                              (uu____13492,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13485 in
                          [uu____13484] in
                        uu____13444 :: uu____13481 in
                      xtok_decl :: uu____13441 in
                    xname_decl :: uu____13438 in
                  (xtok1, uu____13435) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13595 =
                    let uu____13608 =
                      let uu____13617 =
                        let uu____13618 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13618 in
                      quant axy uu____13617 in
                    (FStar_Parser_Const.op_Eq, uu____13608) in
                  let uu____13627 =
                    let uu____13642 =
                      let uu____13655 =
                        let uu____13664 =
                          let uu____13665 =
                            let uu____13666 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13666 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13665 in
                        quant axy uu____13664 in
                      (FStar_Parser_Const.op_notEq, uu____13655) in
                    let uu____13675 =
                      let uu____13690 =
                        let uu____13703 =
                          let uu____13712 =
                            let uu____13713 =
                              let uu____13714 =
                                let uu____13719 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13720 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13719, uu____13720) in
                              FStar_SMTEncoding_Util.mkLT uu____13714 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13713 in
                          quant xy uu____13712 in
                        (FStar_Parser_Const.op_LT, uu____13703) in
                      let uu____13729 =
                        let uu____13744 =
                          let uu____13757 =
                            let uu____13766 =
                              let uu____13767 =
                                let uu____13768 =
                                  let uu____13773 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13774 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13773, uu____13774) in
                                FStar_SMTEncoding_Util.mkLTE uu____13768 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13767 in
                            quant xy uu____13766 in
                          (FStar_Parser_Const.op_LTE, uu____13757) in
                        let uu____13783 =
                          let uu____13798 =
                            let uu____13811 =
                              let uu____13820 =
                                let uu____13821 =
                                  let uu____13822 =
                                    let uu____13827 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13828 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13827, uu____13828) in
                                  FStar_SMTEncoding_Util.mkGT uu____13822 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13821 in
                              quant xy uu____13820 in
                            (FStar_Parser_Const.op_GT, uu____13811) in
                          let uu____13837 =
                            let uu____13852 =
                              let uu____13865 =
                                let uu____13874 =
                                  let uu____13875 =
                                    let uu____13876 =
                                      let uu____13881 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13882 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13881, uu____13882) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13876 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13875 in
                                quant xy uu____13874 in
                              (FStar_Parser_Const.op_GTE, uu____13865) in
                            let uu____13891 =
                              let uu____13906 =
                                let uu____13919 =
                                  let uu____13928 =
                                    let uu____13929 =
                                      let uu____13930 =
                                        let uu____13935 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13936 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13935, uu____13936) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13930 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13929 in
                                  quant xy uu____13928 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13919) in
                              let uu____13945 =
                                let uu____13960 =
                                  let uu____13973 =
                                    let uu____13982 =
                                      let uu____13983 =
                                        let uu____13984 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13984 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13983 in
                                    quant qx uu____13982 in
                                  (FStar_Parser_Const.op_Minus, uu____13973) in
                                let uu____13993 =
                                  let uu____14008 =
                                    let uu____14021 =
                                      let uu____14030 =
                                        let uu____14031 =
                                          let uu____14032 =
                                            let uu____14037 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14038 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14037, uu____14038) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14032 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14031 in
                                      quant xy uu____14030 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14021) in
                                  let uu____14047 =
                                    let uu____14062 =
                                      let uu____14075 =
                                        let uu____14084 =
                                          let uu____14085 =
                                            let uu____14086 =
                                              let uu____14091 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14092 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14091, uu____14092) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14086 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14085 in
                                        quant xy uu____14084 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14075) in
                                    let uu____14101 =
                                      let uu____14116 =
                                        let uu____14129 =
                                          let uu____14138 =
                                            let uu____14139 =
                                              let uu____14140 =
                                                let uu____14145 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14146 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14145, uu____14146) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14140 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14139 in
                                          quant xy uu____14138 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14129) in
                                      let uu____14155 =
                                        let uu____14170 =
                                          let uu____14183 =
                                            let uu____14192 =
                                              let uu____14193 =
                                                let uu____14194 =
                                                  let uu____14199 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14200 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14199, uu____14200) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14194 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14193 in
                                            quant xy uu____14192 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14183) in
                                        let uu____14209 =
                                          let uu____14224 =
                                            let uu____14237 =
                                              let uu____14246 =
                                                let uu____14247 =
                                                  let uu____14248 =
                                                    let uu____14253 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14254 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14253,
                                                      uu____14254) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14248 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14247 in
                                              quant xy uu____14246 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14237) in
                                          let uu____14263 =
                                            let uu____14278 =
                                              let uu____14291 =
                                                let uu____14300 =
                                                  let uu____14301 =
                                                    let uu____14302 =
                                                      let uu____14307 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14308 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14307,
                                                        uu____14308) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14302 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14301 in
                                                quant xy uu____14300 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14291) in
                                            let uu____14317 =
                                              let uu____14332 =
                                                let uu____14345 =
                                                  let uu____14354 =
                                                    let uu____14355 =
                                                      let uu____14356 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14356 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14355 in
                                                  quant qx uu____14354 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14345) in
                                              [uu____14332] in
                                            uu____14278 :: uu____14317 in
                                          uu____14224 :: uu____14263 in
                                        uu____14170 :: uu____14209 in
                                      uu____14116 :: uu____14155 in
                                    uu____14062 :: uu____14101 in
                                  uu____14008 :: uu____14047 in
                                uu____13960 :: uu____13993 in
                              uu____13906 :: uu____13945 in
                            uu____13852 :: uu____13891 in
                          uu____13798 :: uu____13837 in
                        uu____13744 :: uu____13783 in
                      uu____13690 :: uu____13729 in
                    uu____13642 :: uu____13675 in
                  uu____13595 :: uu____13627 in
                let mk1 l v1 =
                  let uu____14570 =
                    let uu____14579 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14637  ->
                              match uu____14637 with
                              | (l',uu____14651) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14579
                      (FStar_Option.map
                         (fun uu____14711  ->
                            match uu____14711 with | (uu____14730,b) -> b v1)) in
                  FStar_All.pipe_right uu____14570 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14801  ->
                          match uu____14801 with
                          | (l',uu____14815) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14856 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14856 with
        | (xxsym,xx) ->
            let uu____14863 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14863 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14873 =
                   let uu____14880 =
                     let uu____14881 =
                       let uu____14892 =
                         let uu____14893 =
                           let uu____14898 =
                             let uu____14899 =
                               let uu____14904 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14904) in
                             FStar_SMTEncoding_Util.mkEq uu____14899 in
                           (xx_has_type, uu____14898) in
                         FStar_SMTEncoding_Util.mkImp uu____14893 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14892) in
                     FStar_SMTEncoding_Util.mkForall uu____14881 in
                   let uu____14929 =
                     let uu____14930 =
                       let uu____14931 =
                         let uu____14932 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14932 in
                       Prims.strcat module_name uu____14931 in
                     varops.mk_unique uu____14930 in
                   (uu____14880, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14929) in
                 FStar_SMTEncoding_Util.mkAssume uu____14873)
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
    let uu____14972 =
      let uu____14973 =
        let uu____14980 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14980, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14973 in
    let uu____14983 =
      let uu____14986 =
        let uu____14987 =
          let uu____14994 =
            let uu____14995 =
              let uu____15006 =
                let uu____15007 =
                  let uu____15012 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15012) in
                FStar_SMTEncoding_Util.mkImp uu____15007 in
              ([[typing_pred]], [xx], uu____15006) in
            mkForall_fuel uu____14995 in
          (uu____14994, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14987 in
      [uu____14986] in
    uu____14972 :: uu____14983 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15054 =
      let uu____15055 =
        let uu____15062 =
          let uu____15063 =
            let uu____15074 =
              let uu____15079 =
                let uu____15082 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15082] in
              [uu____15079] in
            let uu____15087 =
              let uu____15088 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15088 tt in
            (uu____15074, [bb], uu____15087) in
          FStar_SMTEncoding_Util.mkForall uu____15063 in
        (uu____15062, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15055 in
    let uu____15109 =
      let uu____15112 =
        let uu____15113 =
          let uu____15120 =
            let uu____15121 =
              let uu____15132 =
                let uu____15133 =
                  let uu____15138 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15138) in
                FStar_SMTEncoding_Util.mkImp uu____15133 in
              ([[typing_pred]], [xx], uu____15132) in
            mkForall_fuel uu____15121 in
          (uu____15120, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15113 in
      [uu____15112] in
    uu____15054 :: uu____15109 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15188 =
        let uu____15189 =
          let uu____15196 =
            let uu____15199 =
              let uu____15202 =
                let uu____15205 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15206 =
                  let uu____15209 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15209] in
                uu____15205 :: uu____15206 in
              tt :: uu____15202 in
            tt :: uu____15199 in
          ("Prims.Precedes", uu____15196) in
        FStar_SMTEncoding_Util.mkApp uu____15189 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15188 in
    let precedes_y_x =
      let uu____15213 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15213 in
    let uu____15216 =
      let uu____15217 =
        let uu____15224 =
          let uu____15225 =
            let uu____15236 =
              let uu____15241 =
                let uu____15244 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15244] in
              [uu____15241] in
            let uu____15249 =
              let uu____15250 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15250 tt in
            (uu____15236, [bb], uu____15249) in
          FStar_SMTEncoding_Util.mkForall uu____15225 in
        (uu____15224, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15217 in
    let uu____15271 =
      let uu____15274 =
        let uu____15275 =
          let uu____15282 =
            let uu____15283 =
              let uu____15294 =
                let uu____15295 =
                  let uu____15300 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15300) in
                FStar_SMTEncoding_Util.mkImp uu____15295 in
              ([[typing_pred]], [xx], uu____15294) in
            mkForall_fuel uu____15283 in
          (uu____15282, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15275 in
      let uu____15325 =
        let uu____15328 =
          let uu____15329 =
            let uu____15336 =
              let uu____15337 =
                let uu____15348 =
                  let uu____15349 =
                    let uu____15354 =
                      let uu____15355 =
                        let uu____15358 =
                          let uu____15361 =
                            let uu____15364 =
                              let uu____15365 =
                                let uu____15370 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15371 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15370, uu____15371) in
                              FStar_SMTEncoding_Util.mkGT uu____15365 in
                            let uu____15372 =
                              let uu____15375 =
                                let uu____15376 =
                                  let uu____15381 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15382 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15381, uu____15382) in
                                FStar_SMTEncoding_Util.mkGTE uu____15376 in
                              let uu____15383 =
                                let uu____15386 =
                                  let uu____15387 =
                                    let uu____15392 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15393 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15392, uu____15393) in
                                  FStar_SMTEncoding_Util.mkLT uu____15387 in
                                [uu____15386] in
                              uu____15375 :: uu____15383 in
                            uu____15364 :: uu____15372 in
                          typing_pred_y :: uu____15361 in
                        typing_pred :: uu____15358 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15355 in
                    (uu____15354, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15349 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15348) in
              mkForall_fuel uu____15337 in
            (uu____15336,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15329 in
        [uu____15328] in
      uu____15274 :: uu____15325 in
    uu____15216 :: uu____15271 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15439 =
      let uu____15440 =
        let uu____15447 =
          let uu____15448 =
            let uu____15459 =
              let uu____15464 =
                let uu____15467 = FStar_SMTEncoding_Term.boxString b in
                [uu____15467] in
              [uu____15464] in
            let uu____15472 =
              let uu____15473 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15473 tt in
            (uu____15459, [bb], uu____15472) in
          FStar_SMTEncoding_Util.mkForall uu____15448 in
        (uu____15447, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15440 in
    let uu____15494 =
      let uu____15497 =
        let uu____15498 =
          let uu____15505 =
            let uu____15506 =
              let uu____15517 =
                let uu____15518 =
                  let uu____15523 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15523) in
                FStar_SMTEncoding_Util.mkImp uu____15518 in
              ([[typing_pred]], [xx], uu____15517) in
            mkForall_fuel uu____15506 in
          (uu____15505, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15498 in
      [uu____15497] in
    uu____15439 :: uu____15494 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15576 =
      let uu____15577 =
        let uu____15584 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15584, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15577 in
    [uu____15576] in
  let mk_and_interp env conj uu____15596 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15621 =
      let uu____15622 =
        let uu____15629 =
          let uu____15630 =
            let uu____15641 =
              let uu____15642 =
                let uu____15647 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15647, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15642 in
            ([[l_and_a_b]], [aa; bb], uu____15641) in
          FStar_SMTEncoding_Util.mkForall uu____15630 in
        (uu____15629, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15622 in
    [uu____15621] in
  let mk_or_interp env disj uu____15685 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15710 =
      let uu____15711 =
        let uu____15718 =
          let uu____15719 =
            let uu____15730 =
              let uu____15731 =
                let uu____15736 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15736, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15731 in
            ([[l_or_a_b]], [aa; bb], uu____15730) in
          FStar_SMTEncoding_Util.mkForall uu____15719 in
        (uu____15718, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15711 in
    [uu____15710] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15799 =
      let uu____15800 =
        let uu____15807 =
          let uu____15808 =
            let uu____15819 =
              let uu____15820 =
                let uu____15825 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15825, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15820 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15819) in
          FStar_SMTEncoding_Util.mkForall uu____15808 in
        (uu____15807, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15800 in
    [uu____15799] in
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
    let uu____15898 =
      let uu____15899 =
        let uu____15906 =
          let uu____15907 =
            let uu____15918 =
              let uu____15919 =
                let uu____15924 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15924, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15919 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15918) in
          FStar_SMTEncoding_Util.mkForall uu____15907 in
        (uu____15906, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15899 in
    [uu____15898] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15995 =
      let uu____15996 =
        let uu____16003 =
          let uu____16004 =
            let uu____16015 =
              let uu____16016 =
                let uu____16021 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16021, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16016 in
            ([[l_imp_a_b]], [aa; bb], uu____16015) in
          FStar_SMTEncoding_Util.mkForall uu____16004 in
        (uu____16003, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15996 in
    [uu____15995] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16084 =
      let uu____16085 =
        let uu____16092 =
          let uu____16093 =
            let uu____16104 =
              let uu____16105 =
                let uu____16110 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16110, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16105 in
            ([[l_iff_a_b]], [aa; bb], uu____16104) in
          FStar_SMTEncoding_Util.mkForall uu____16093 in
        (uu____16092, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16085 in
    [uu____16084] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16162 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16162 in
    let uu____16165 =
      let uu____16166 =
        let uu____16173 =
          let uu____16174 =
            let uu____16185 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16185) in
          FStar_SMTEncoding_Util.mkForall uu____16174 in
        (uu____16173, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16166 in
    [uu____16165] in
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
      let uu____16245 =
        let uu____16252 =
          let uu____16255 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16255] in
        ("Valid", uu____16252) in
      FStar_SMTEncoding_Util.mkApp uu____16245 in
    let uu____16258 =
      let uu____16259 =
        let uu____16266 =
          let uu____16267 =
            let uu____16278 =
              let uu____16279 =
                let uu____16284 =
                  let uu____16285 =
                    let uu____16296 =
                      let uu____16301 =
                        let uu____16304 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16304] in
                      [uu____16301] in
                    let uu____16309 =
                      let uu____16310 =
                        let uu____16315 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16315, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16310 in
                    (uu____16296, [xx1], uu____16309) in
                  FStar_SMTEncoding_Util.mkForall uu____16285 in
                (uu____16284, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16279 in
            ([[l_forall_a_b]], [aa; bb], uu____16278) in
          FStar_SMTEncoding_Util.mkForall uu____16267 in
        (uu____16266, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16259 in
    [uu____16258] in
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
      let uu____16397 =
        let uu____16404 =
          let uu____16407 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16407] in
        ("Valid", uu____16404) in
      FStar_SMTEncoding_Util.mkApp uu____16397 in
    let uu____16410 =
      let uu____16411 =
        let uu____16418 =
          let uu____16419 =
            let uu____16430 =
              let uu____16431 =
                let uu____16436 =
                  let uu____16437 =
                    let uu____16448 =
                      let uu____16453 =
                        let uu____16456 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16456] in
                      [uu____16453] in
                    let uu____16461 =
                      let uu____16462 =
                        let uu____16467 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16467, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16462 in
                    (uu____16448, [xx1], uu____16461) in
                  FStar_SMTEncoding_Util.mkExists uu____16437 in
                (uu____16436, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16431 in
            ([[l_exists_a_b]], [aa; bb], uu____16430) in
          FStar_SMTEncoding_Util.mkForall uu____16419 in
        (uu____16418, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16411 in
    [uu____16410] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16527 =
      let uu____16528 =
        let uu____16535 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16536 = varops.mk_unique "typing_range_const" in
        (uu____16535, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16536) in
      FStar_SMTEncoding_Util.mkAssume uu____16528 in
    [uu____16527] in
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
        let uu____16570 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16570 x1 t in
      let uu____16571 =
        let uu____16582 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16582) in
      FStar_SMTEncoding_Util.mkForall uu____16571 in
    let uu____16605 =
      let uu____16606 =
        let uu____16613 =
          let uu____16614 =
            let uu____16625 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16625) in
          FStar_SMTEncoding_Util.mkForall uu____16614 in
        (uu____16613,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16606 in
    [uu____16605] in
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
          let uu____16949 =
            FStar_Util.find_opt
              (fun uu____16975  ->
                 match uu____16975 with
                 | (l,uu____16987) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16949 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17012,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17051 = encode_function_type_as_formula t env in
        match uu____17051 with
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
              let uu____17097 =
                ((let uu____17100 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17100) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17097
              then
                let uu____17107 = new_term_constant_and_tok_from_lid env lid in
                match uu____17107 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17126 =
                        let uu____17127 = FStar_Syntax_Subst.compress t_norm in
                        uu____17127.FStar_Syntax_Syntax.n in
                      match uu____17126 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17133) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17163  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17168 -> [] in
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
                (let uu____17182 = prims.is lid in
                 if uu____17182
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17190 = prims.mk lid vname in
                   match uu____17190 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17214 =
                      let uu____17225 = curried_arrow_formals_comp t_norm in
                      match uu____17225 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17243 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17243
                            then
                              let uu____17244 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___149_17247 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___149_17247.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___149_17247.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___149_17247.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___149_17247.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___149_17247.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___149_17247.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___149_17247.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___149_17247.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___149_17247.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___149_17247.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___149_17247.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___149_17247.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___149_17247.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___149_17247.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___149_17247.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___149_17247.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___149_17247.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___149_17247.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___149_17247.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___149_17247.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___149_17247.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___149_17247.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___149_17247.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___149_17247.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___149_17247.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___149_17247.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___149_17247.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___149_17247.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___149_17247.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17244
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17259 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17259)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17214 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17304 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17304 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17325 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___121_17367  ->
                                       match uu___121_17367 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17371 =
                                             FStar_Util.prefix vars in
                                           (match uu____17371 with
                                            | (uu____17392,(xxsym,uu____17394))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17412 =
                                                  let uu____17413 =
                                                    let uu____17420 =
                                                      let uu____17421 =
                                                        let uu____17432 =
                                                          let uu____17433 =
                                                            let uu____17438 =
                                                              let uu____17439
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17439 in
                                                            (vapp,
                                                              uu____17438) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17433 in
                                                        ([[vapp]], vars,
                                                          uu____17432) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17421 in
                                                    (uu____17420,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17413 in
                                                [uu____17412])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17458 =
                                             FStar_Util.prefix vars in
                                           (match uu____17458 with
                                            | (uu____17479,(xxsym,uu____17481))
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
                                                let uu____17504 =
                                                  let uu____17505 =
                                                    let uu____17512 =
                                                      let uu____17513 =
                                                        let uu____17524 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17524) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17513 in
                                                    (uu____17512,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17505 in
                                                [uu____17504])
                                       | uu____17541 -> [])) in
                             let uu____17542 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17542 with
                              | (vars,guards,env',decls1,uu____17569) ->
                                  let uu____17582 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17591 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17591, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17593 =
                                          encode_formula p env' in
                                        (match uu____17593 with
                                         | (g,ds) ->
                                             let uu____17604 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17604,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17582 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17617 =
                                           let uu____17624 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17624) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17617 in
                                       let uu____17633 =
                                         let vname_decl =
                                           let uu____17641 =
                                             let uu____17652 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17662  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17652,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17641 in
                                         let uu____17671 =
                                           let env2 =
                                             let uu___150_17677 = env1 in
                                             {
                                               bindings =
                                                 (uu___150_17677.bindings);
                                               depth = (uu___150_17677.depth);
                                               tcenv = (uu___150_17677.tcenv);
                                               warn = (uu___150_17677.warn);
                                               cache = (uu___150_17677.cache);
                                               nolabels =
                                                 (uu___150_17677.nolabels);
                                               use_zfuel_name =
                                                 (uu___150_17677.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___150_17677.current_module_name)
                                             } in
                                           let uu____17678 =
                                             let uu____17679 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17679 in
                                           if uu____17678
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17671 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17694::uu____17695 ->
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
                                                     let uu____17735 =
                                                       let uu____17746 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17746) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17735 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17773 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17776 =
                                               match formals with
                                               | [] ->
                                                   let uu____17793 =
                                                     let uu____17794 =
                                                       let uu____17797 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17797 in
                                                     push_free_var env1 lid
                                                       vname uu____17794 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17793)
                                               | uu____17802 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17809 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17809 in
                                                   let name_tok_corr =
                                                     let uu____17811 =
                                                       let uu____17818 =
                                                         let uu____17819 =
                                                           let uu____17830 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17830) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17819 in
                                                       (uu____17818,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17811 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17776 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17633 with
                                        | (decls2,env2) ->
                                            let uu____17873 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17881 =
                                                encode_term res_t1 env' in
                                              match uu____17881 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17894 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17894, decls) in
                                            (match uu____17873 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17905 =
                                                     let uu____17912 =
                                                       let uu____17913 =
                                                         let uu____17924 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17924) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17913 in
                                                     (uu____17912,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17905 in
                                                 let freshness =
                                                   let uu____17940 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17940
                                                   then
                                                     let uu____17945 =
                                                       let uu____17946 =
                                                         let uu____17957 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17968 =
                                                           varops.next_id () in
                                                         (vname, uu____17957,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17968) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17946 in
                                                     let uu____17971 =
                                                       let uu____17974 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17974] in
                                                     uu____17945 ::
                                                       uu____17971
                                                   else [] in
                                                 let g =
                                                   let uu____17979 =
                                                     let uu____17982 =
                                                       let uu____17985 =
                                                         let uu____17988 =
                                                           let uu____17991 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17991 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17988 in
                                                       FStar_List.append
                                                         decls3 uu____17985 in
                                                     FStar_List.append decls2
                                                       uu____17982 in
                                                   FStar_List.append decls11
                                                     uu____17979 in
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
          let uu____18026 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18026 with
          | FStar_Pervasives_Native.None  ->
              let uu____18063 = encode_free_var false env x t t_norm [] in
              (match uu____18063 with
               | (decls,env1) ->
                   let uu____18090 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18090 with
                    | (n1,x',uu____18117) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18138) ->
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
            let uu____18198 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18198 with
            | (decls,env1) ->
                let uu____18217 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18217
                then
                  let uu____18224 =
                    let uu____18227 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18227 in
                  (uu____18224, env1)
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
             (fun uu____18282  ->
                fun lb  ->
                  match uu____18282 with
                  | (decls,env1) ->
                      let uu____18302 =
                        let uu____18309 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18309
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18302 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18331 = FStar_Syntax_Util.head_and_args t in
    match uu____18331 with
    | (hd1,args) ->
        let uu____18368 =
          let uu____18369 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18369.FStar_Syntax_Syntax.n in
        (match uu____18368 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18373,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18392 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18417  ->
      fun quals  ->
        match uu____18417 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18493 = FStar_Util.first_N nbinders formals in
              match uu____18493 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18574  ->
                         fun uu____18575  ->
                           match (uu____18574, uu____18575) with
                           | ((formal,uu____18593),(binder,uu____18595)) ->
                               let uu____18604 =
                                 let uu____18611 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18611) in
                               FStar_Syntax_Syntax.NT uu____18604) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18619 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18650  ->
                              match uu____18650 with
                              | (x,i) ->
                                  let uu____18661 =
                                    let uu___151_18662 = x in
                                    let uu____18663 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___151_18662.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___151_18662.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18663
                                    } in
                                  (uu____18661, i))) in
                    FStar_All.pipe_right uu____18619
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18681 =
                      let uu____18682 = FStar_Syntax_Subst.compress body in
                      let uu____18683 =
                        let uu____18684 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18684 in
                      FStar_Syntax_Syntax.extend_app_n uu____18682
                        uu____18683 in
                    uu____18681 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18745 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18745
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___152_18748 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_18748.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_18748.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_18748.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_18748.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_18748.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_18748.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_18748.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_18748.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_18748.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_18748.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_18748.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_18748.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_18748.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_18748.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_18748.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_18748.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_18748.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_18748.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_18748.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___152_18748.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___152_18748.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_18748.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_18748.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_18748.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_18748.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___152_18748.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___152_18748.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___152_18748.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___152_18748.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18781 = FStar_Syntax_Util.abs_formals e in
                match uu____18781 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18845::uu____18846 ->
                         let uu____18861 =
                           let uu____18862 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18862.FStar_Syntax_Syntax.n in
                         (match uu____18861 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18907 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18907 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18949 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18949
                                   then
                                     let uu____18984 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18984 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19078  ->
                                                   fun uu____19079  ->
                                                     match (uu____19078,
                                                             uu____19079)
                                                     with
                                                     | ((x,uu____19097),
                                                        (b,uu____19099)) ->
                                                         let uu____19108 =
                                                           let uu____19115 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19115) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19108)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19117 =
                                            let uu____19138 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19138) in
                                          (uu____19117, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19206 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19206 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19295) ->
                              let uu____19300 =
                                let uu____19321 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19321 in
                              (uu____19300, true)
                          | uu____19386 when Prims.op_Negation norm1 ->
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
                          | uu____19388 ->
                              let uu____19389 =
                                let uu____19390 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19391 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19390
                                  uu____19391 in
                              failwith uu____19389)
                     | uu____19416 ->
                         let uu____19417 =
                           let uu____19418 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19418.FStar_Syntax_Syntax.n in
                         (match uu____19417 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19463 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19463 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19495 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19495 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19578 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19634 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19634
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19646 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19740  ->
                            fun lb  ->
                              match uu____19740 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19835 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19835
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19838 =
                                      let uu____19853 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19853
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19838 with
                                    | (tok,decl,env2) ->
                                        let uu____19899 =
                                          let uu____19912 =
                                            let uu____19923 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19923, tok) in
                                          uu____19912 :: toks in
                                        (uu____19899, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19646 with
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
                        | uu____20106 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20114 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20114 vars)
                            else
                              (let uu____20116 =
                                 let uu____20123 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20123) in
                               FStar_SMTEncoding_Util.mkApp uu____20116) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20205;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20207;
                             FStar_Syntax_Syntax.lbeff = uu____20208;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20271 =
                              let uu____20278 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20278 with
                              | (tcenv',uu____20296,e_t) ->
                                  let uu____20302 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20313 -> failwith "Impossible" in
                                  (match uu____20302 with
                                   | (e1,t_norm1) ->
                                       ((let uu___155_20329 = env2 in
                                         {
                                           bindings =
                                             (uu___155_20329.bindings);
                                           depth = (uu___155_20329.depth);
                                           tcenv = tcenv';
                                           warn = (uu___155_20329.warn);
                                           cache = (uu___155_20329.cache);
                                           nolabels =
                                             (uu___155_20329.nolabels);
                                           use_zfuel_name =
                                             (uu___155_20329.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___155_20329.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___155_20329.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20271 with
                             | (env',e1,t_norm1) ->
                                 let uu____20339 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20339 with
                                  | ((binders,body,uu____20360,uu____20361),curry)
                                      ->
                                      ((let uu____20372 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20372
                                        then
                                          let uu____20373 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20374 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20373 uu____20374
                                        else ());
                                       (let uu____20376 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20376 with
                                        | (vars,guards,env'1,binder_decls,uu____20403)
                                            ->
                                            let body1 =
                                              let uu____20417 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20417
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20420 =
                                              let uu____20429 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20429
                                              then
                                                let uu____20440 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20441 =
                                                  encode_formula body1 env'1 in
                                                (uu____20440, uu____20441)
                                              else
                                                (let uu____20451 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20451)) in
                                            (match uu____20420 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20474 =
                                                     let uu____20481 =
                                                       let uu____20482 =
                                                         let uu____20493 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20493) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20482 in
                                                     let uu____20504 =
                                                       let uu____20507 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20507 in
                                                     (uu____20481,
                                                       uu____20504,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20474 in
                                                 let uu____20510 =
                                                   let uu____20513 =
                                                     let uu____20516 =
                                                       let uu____20519 =
                                                         let uu____20522 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20522 in
                                                       FStar_List.append
                                                         decls2 uu____20519 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20516 in
                                                   FStar_List.append decls1
                                                     uu____20513 in
                                                 (uu____20510, env2))))))
                        | uu____20527 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20612 = varops.fresh "fuel" in
                          (uu____20612, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20615 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20703  ->
                                  fun uu____20704  ->
                                    match (uu____20703, uu____20704) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20852 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20852 in
                                        let gtok =
                                          let uu____20854 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20854 in
                                        let env4 =
                                          let uu____20856 =
                                            let uu____20859 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20859 in
                                          push_free_var env3 flid gtok
                                            uu____20856 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20615 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____21015 t_norm
                              uu____21017 =
                              match (uu____21015, uu____21017) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21061;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21062;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21090 =
                                    let uu____21097 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____21097 with
                                    | (tcenv',uu____21119,e_t) ->
                                        let uu____21125 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21136 ->
                                              failwith "Impossible" in
                                        (match uu____21125 with
                                         | (e1,t_norm1) ->
                                             ((let uu___156_21152 = env3 in
                                               {
                                                 bindings =
                                                   (uu___156_21152.bindings);
                                                 depth =
                                                   (uu___156_21152.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___156_21152.warn);
                                                 cache =
                                                   (uu___156_21152.cache);
                                                 nolabels =
                                                   (uu___156_21152.nolabels);
                                                 use_zfuel_name =
                                                   (uu___156_21152.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___156_21152.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___156_21152.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____21090 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21167 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21167
                                         then
                                           let uu____21168 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21169 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21170 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21168 uu____21169
                                             uu____21170
                                         else ());
                                        (let uu____21172 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21172 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21209 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21209
                                               then
                                                 let uu____21210 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21211 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21212 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21213 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21210 uu____21211
                                                   uu____21212 uu____21213
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21217 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21217 with
                                               | (vars,guards,env'1,binder_decls,uu____21248)
                                                   ->
                                                   let decl_g =
                                                     let uu____21262 =
                                                       let uu____21273 =
                                                         let uu____21276 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21276 in
                                                       (g, uu____21273,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21262 in
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
                                                     let uu____21301 =
                                                       let uu____21308 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21308) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21301 in
                                                   let gsapp =
                                                     let uu____21318 =
                                                       let uu____21325 =
                                                         let uu____21328 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21328 ::
                                                           vars_tm in
                                                       (g, uu____21325) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21318 in
                                                   let gmax =
                                                     let uu____21334 =
                                                       let uu____21341 =
                                                         let uu____21344 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21344 ::
                                                           vars_tm in
                                                       (g, uu____21341) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21334 in
                                                   let body1 =
                                                     let uu____21350 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21350
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21352 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21352 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21370 =
                                                            let uu____21377 =
                                                              let uu____21378
                                                                =
                                                                let uu____21393
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
                                                                  uu____21393) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21378 in
                                                            let uu____21414 =
                                                              let uu____21417
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21417 in
                                                            (uu____21377,
                                                              uu____21414,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21370 in
                                                        let eqn_f =
                                                          let uu____21421 =
                                                            let uu____21428 =
                                                              let uu____21429
                                                                =
                                                                let uu____21440
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21440) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21429 in
                                                            (uu____21428,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21421 in
                                                        let eqn_g' =
                                                          let uu____21454 =
                                                            let uu____21461 =
                                                              let uu____21462
                                                                =
                                                                let uu____21473
                                                                  =
                                                                  let uu____21474
                                                                    =
                                                                    let uu____21479
                                                                    =
                                                                    let uu____21480
                                                                    =
                                                                    let uu____21487
                                                                    =
                                                                    let uu____21490
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21490
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21487) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21480 in
                                                                    (gsapp,
                                                                    uu____21479) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21474 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21473) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21462 in
                                                            (uu____21461,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21454 in
                                                        let uu____21513 =
                                                          let uu____21522 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21522
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21551)
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
                                                                  let uu____21576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21576
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21581
                                                                  =
                                                                  let uu____21588
                                                                    =
                                                                    let uu____21589
                                                                    =
                                                                    let uu____21600
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21600) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21589 in
                                                                  (uu____21588,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21581 in
                                                              let uu____21621
                                                                =
                                                                let uu____21628
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21628
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21641
                                                                    =
                                                                    let uu____21644
                                                                    =
                                                                    let uu____21645
                                                                    =
                                                                    let uu____21652
                                                                    =
                                                                    let uu____21653
                                                                    =
                                                                    let uu____21664
                                                                    =
                                                                    let uu____21665
                                                                    =
                                                                    let uu____21670
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21670,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21665 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21664) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21653 in
                                                                    (uu____21652,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21645 in
                                                                    [uu____21644] in
                                                                    (d3,
                                                                    uu____21641) in
                                                              (match uu____21621
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21513
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
                            let uu____21735 =
                              let uu____21748 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21827  ->
                                   fun uu____21828  ->
                                     match (uu____21827, uu____21828) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21983 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21983 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21748 in
                            (match uu____21735 with
                             | (decls2,eqns,env01) ->
                                 let uu____22056 =
                                   let isDeclFun uu___122_22068 =
                                     match uu___122_22068 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22069 -> true
                                     | uu____22080 -> false in
                                   let uu____22081 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____22081
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____22056 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____22121 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___123_22125  ->
                                 match uu___123_22125 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22126 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22132 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22132))) in
                      if uu____22121
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
                   let uu____22184 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22184
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
        let uu____22233 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22233 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22237 = encode_sigelt' env se in
      match uu____22237 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22253 =
                  let uu____22254 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22254 in
                [uu____22253]
            | uu____22255 ->
                let uu____22256 =
                  let uu____22259 =
                    let uu____22260 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22260 in
                  uu____22259 :: g in
                let uu____22261 =
                  let uu____22264 =
                    let uu____22265 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22265 in
                  [uu____22264] in
                FStar_List.append uu____22256 uu____22261 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22278 =
          let uu____22279 = FStar_Syntax_Subst.compress t in
          uu____22279.FStar_Syntax_Syntax.n in
        match uu____22278 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22283)) -> s = "opaque_to_smt"
        | uu____22284 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22289 =
          let uu____22290 = FStar_Syntax_Subst.compress t in
          uu____22290.FStar_Syntax_Syntax.n in
        match uu____22289 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22294)) -> s = "uninterpreted_by_smt"
        | uu____22295 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22300 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22305 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22308 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22311 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22326 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22330 =
            let uu____22331 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22331 Prims.op_Negation in
          if uu____22330
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22357 ->
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
               let uu____22377 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22377 with
               | (aname,atok,env2) ->
                   let uu____22393 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22393 with
                    | (formals,uu____22411) ->
                        let uu____22424 =
                          let uu____22429 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22429 env2 in
                        (match uu____22424 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22441 =
                                 let uu____22442 =
                                   let uu____22453 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22469  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22453,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22442 in
                               [uu____22441;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22482 =
                               let aux uu____22534 uu____22535 =
                                 match (uu____22534, uu____22535) with
                                 | ((bv,uu____22587),(env3,acc_sorts,acc)) ->
                                     let uu____22625 = gen_term_var env3 bv in
                                     (match uu____22625 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22482 with
                              | (uu____22697,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22720 =
                                      let uu____22727 =
                                        let uu____22728 =
                                          let uu____22739 =
                                            let uu____22740 =
                                              let uu____22745 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22745) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22740 in
                                          ([[app]], xs_sorts, uu____22739) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22728 in
                                      (uu____22727,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22720 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22765 =
                                      let uu____22772 =
                                        let uu____22773 =
                                          let uu____22784 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22784) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22773 in
                                      (uu____22772,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22765 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22803 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22803 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22831,uu____22832)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22833 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22833 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22850,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22856 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___124_22860  ->
                      match uu___124_22860 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22861 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22866 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22867 -> false)) in
            Prims.op_Negation uu____22856 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22876 =
               let uu____22883 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22883 env fv t quals in
             match uu____22876 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22898 =
                   let uu____22901 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22901 in
                 (uu____22898, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22909 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22909 with
           | (uu____22918,f1) ->
               let uu____22920 = encode_formula f1 env in
               (match uu____22920 with
                | (f2,decls) ->
                    let g =
                      let uu____22934 =
                        let uu____22935 =
                          let uu____22942 =
                            let uu____22945 =
                              let uu____22946 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22946 in
                            FStar_Pervasives_Native.Some uu____22945 in
                          let uu____22947 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22942, uu____22947) in
                        FStar_SMTEncoding_Util.mkAssume uu____22935 in
                      [uu____22934] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22953) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22965 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22983 =
                       let uu____22986 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22986.FStar_Syntax_Syntax.fv_name in
                     uu____22983.FStar_Syntax_Syntax.v in
                   let uu____22987 =
                     let uu____22988 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22988 in
                   if uu____22987
                   then
                     let val_decl =
                       let uu___159_23016 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___159_23016.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___159_23016.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___159_23016.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23021 = encode_sigelt' env1 val_decl in
                     match uu____23021 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22965 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23049,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23051;
                          FStar_Syntax_Syntax.lbtyp = uu____23052;
                          FStar_Syntax_Syntax.lbeff = uu____23053;
                          FStar_Syntax_Syntax.lbdef = uu____23054;_}::[]),uu____23055)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23074 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23074 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23103 =
                   let uu____23106 =
                     let uu____23107 =
                       let uu____23114 =
                         let uu____23115 =
                           let uu____23126 =
                             let uu____23127 =
                               let uu____23132 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23132) in
                             FStar_SMTEncoding_Util.mkEq uu____23127 in
                           ([[b2t_x]], [xx], uu____23126) in
                         FStar_SMTEncoding_Util.mkForall uu____23115 in
                       (uu____23114,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23107 in
                   [uu____23106] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23103 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23165,uu____23166) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_23175  ->
                  match uu___125_23175 with
                  | FStar_Syntax_Syntax.Discriminator uu____23176 -> true
                  | uu____23177 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23180,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23191 =
                     let uu____23192 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23192.FStar_Ident.idText in
                   uu____23191 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___126_23196  ->
                     match uu___126_23196 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23197 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23201) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___127_23218  ->
                  match uu___127_23218 with
                  | FStar_Syntax_Syntax.Projector uu____23219 -> true
                  | uu____23224 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23227 = try_lookup_free_var env l in
          (match uu____23227 with
           | FStar_Pervasives_Native.Some uu____23234 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___160_23238 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___160_23238.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___160_23238.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___160_23238.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23245) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23263) ->
          let uu____23272 = encode_sigelts env ses in
          (match uu____23272 with
           | (g,env1) ->
               let uu____23289 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___128_23312  ->
                         match uu___128_23312 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23313;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23314;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23315;_}
                             -> false
                         | uu____23318 -> true)) in
               (match uu____23289 with
                | (g',inversions) ->
                    let uu____23333 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___129_23354  ->
                              match uu___129_23354 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23355 ->
                                  true
                              | uu____23366 -> false)) in
                    (match uu____23333 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23384,tps,k,uu____23387,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___130_23404  ->
                    match uu___130_23404 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23405 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23414 = c in
              match uu____23414 with
              | (name,args,uu____23419,uu____23420,uu____23421) ->
                  let uu____23426 =
                    let uu____23427 =
                      let uu____23438 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23455  ->
                                match uu____23455 with
                                | (uu____23462,sort,uu____23464) -> sort)) in
                      (name, uu____23438, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23427 in
                  [uu____23426]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23491 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23497 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23497 FStar_Option.isNone)) in
            if uu____23491
            then []
            else
              (let uu____23529 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23529 with
               | (xxsym,xx) ->
                   let uu____23538 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23577  ->
                             fun l  ->
                               match uu____23577 with
                               | (out,decls) ->
                                   let uu____23597 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23597 with
                                    | (uu____23608,data_t) ->
                                        let uu____23610 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23610 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23656 =
                                                 let uu____23657 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23657.FStar_Syntax_Syntax.n in
                                               match uu____23656 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23668,indices) ->
                                                   indices
                                               | uu____23690 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23714  ->
                                                         match uu____23714
                                                         with
                                                         | (x,uu____23720) ->
                                                             let uu____23721
                                                               =
                                                               let uu____23722
                                                                 =
                                                                 let uu____23729
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23729,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23722 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23721)
                                                    env) in
                                             let uu____23732 =
                                               encode_args indices env1 in
                                             (match uu____23732 with
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
                                                      let uu____23758 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23774
                                                                 =
                                                                 let uu____23779
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23779,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23774)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23758
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23782 =
                                                      let uu____23783 =
                                                        let uu____23788 =
                                                          let uu____23789 =
                                                            let uu____23794 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23794,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23789 in
                                                        (out, uu____23788) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23783 in
                                                    (uu____23782,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23538 with
                    | (data_ax,decls) ->
                        let uu____23807 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23807 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23818 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23818 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23822 =
                                 let uu____23829 =
                                   let uu____23830 =
                                     let uu____23841 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23856 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23841,
                                       uu____23856) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23830 in
                                 let uu____23871 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23829,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23871) in
                               FStar_SMTEncoding_Util.mkAssume uu____23822 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23874 =
            let uu____23887 =
              let uu____23888 = FStar_Syntax_Subst.compress k in
              uu____23888.FStar_Syntax_Syntax.n in
            match uu____23887 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23933 -> (tps, k) in
          (match uu____23874 with
           | (formals,res) ->
               let uu____23956 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23956 with
                | (formals1,res1) ->
                    let uu____23967 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23967 with
                     | (vars,guards,env',binder_decls,uu____23992) ->
                         let uu____24005 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____24005 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24024 =
                                  let uu____24031 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24031) in
                                FStar_SMTEncoding_Util.mkApp uu____24024 in
                              let uu____24040 =
                                let tname_decl =
                                  let uu____24050 =
                                    let uu____24051 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24083  ->
                                              match uu____24083 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24096 = varops.next_id () in
                                    (tname, uu____24051,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24096, false) in
                                  constructor_or_logic_type_decl uu____24050 in
                                let uu____24105 =
                                  match vars with
                                  | [] ->
                                      let uu____24118 =
                                        let uu____24119 =
                                          let uu____24122 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____24122 in
                                        push_free_var env1 t tname
                                          uu____24119 in
                                      ([], uu____24118)
                                  | uu____24129 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24138 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24138 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24152 =
                                          let uu____24159 =
                                            let uu____24160 =
                                              let uu____24175 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24175) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24160 in
                                          (uu____24159,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24152 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24105 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24040 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24215 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24215 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24233 =
                                               let uu____24234 =
                                                 let uu____24241 =
                                                   let uu____24242 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24242 in
                                                 (uu____24241,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24234 in
                                             [uu____24233]
                                           else [] in
                                         let uu____24246 =
                                           let uu____24249 =
                                             let uu____24252 =
                                               let uu____24253 =
                                                 let uu____24260 =
                                                   let uu____24261 =
                                                     let uu____24272 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24272) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24261 in
                                                 (uu____24260,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24253 in
                                             [uu____24252] in
                                           FStar_List.append karr uu____24249 in
                                         FStar_List.append decls1 uu____24246 in
                                   let aux =
                                     let uu____24288 =
                                       let uu____24291 =
                                         inversion_axioms tapp vars in
                                       let uu____24294 =
                                         let uu____24297 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24297] in
                                       FStar_List.append uu____24291
                                         uu____24294 in
                                     FStar_List.append kindingAx uu____24288 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24304,uu____24305,uu____24306,uu____24307,uu____24308)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24316,t,uu____24318,n_tps,uu____24320) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24328 = new_term_constant_and_tok_from_lid env d in
          (match uu____24328 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24345 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24345 with
                | (formals,t_res) ->
                    let uu____24380 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24380 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24394 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24394 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24464 =
                                            mk_term_projector_name d x in
                                          (uu____24464,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24466 =
                                  let uu____24485 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24485, true) in
                                FStar_All.pipe_right uu____24466
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
                              let uu____24524 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24524 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24536::uu____24537 ->
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
                                         let uu____24582 =
                                           let uu____24593 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24593) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24582
                                     | uu____24618 -> tok_typing in
                                   let uu____24627 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24627 with
                                    | (vars',guards',env'',decls_formals,uu____24652)
                                        ->
                                        let uu____24665 =
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
                                        (match uu____24665 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24696 ->
                                                   let uu____24703 =
                                                     let uu____24704 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24704 in
                                                   [uu____24703] in
                                             let encode_elim uu____24714 =
                                               let uu____24715 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24715 with
                                               | (head1,args) ->
                                                   let uu____24758 =
                                                     let uu____24759 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24759.FStar_Syntax_Syntax.n in
                                                   (match uu____24758 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24769;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24770;_},uu____24771)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24777 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24777
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
                                                                 | uu____24820
                                                                    ->
                                                                    let uu____24821
                                                                    =
                                                                    let uu____24822
                                                                    =
                                                                    let uu____24827
                                                                    =
                                                                    let uu____24828
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24828 in
                                                                    (uu____24827,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24822 in
                                                                    FStar_Exn.raise
                                                                    uu____24821 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24844
                                                                    =
                                                                    let uu____24845
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24845 in
                                                                    if
                                                                    uu____24844
                                                                    then
                                                                    let uu____24858
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24858]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24860
                                                               =
                                                               let uu____24873
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24923
                                                                     ->
                                                                    fun
                                                                    uu____24924
                                                                     ->
                                                                    match 
                                                                    (uu____24923,
                                                                    uu____24924)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25019
                                                                    =
                                                                    let uu____25026
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25026 in
                                                                    (match uu____25019
                                                                    with
                                                                    | 
                                                                    (uu____25039,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25047
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25047
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25049
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25049
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
                                                                 uu____24873 in
                                                             (match uu____24860
                                                              with
                                                              | (uu____25064,arg_vars,elim_eqns_or_guards,uu____25067)
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
                                                                    let uu____25097
                                                                    =
                                                                    let uu____25104
                                                                    =
                                                                    let uu____25105
                                                                    =
                                                                    let uu____25116
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25127
                                                                    =
                                                                    let uu____25128
                                                                    =
                                                                    let uu____25133
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25133) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25128 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25116,
                                                                    uu____25127) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25105 in
                                                                    (uu____25104,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25097 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25156
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25156,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25158
                                                                    =
                                                                    let uu____25165
                                                                    =
                                                                    let uu____25166
                                                                    =
                                                                    let uu____25177
                                                                    =
                                                                    let uu____25182
                                                                    =
                                                                    let uu____25185
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25185] in
                                                                    [uu____25182] in
                                                                    let uu____25190
                                                                    =
                                                                    let uu____25191
                                                                    =
                                                                    let uu____25196
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25197
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25196,
                                                                    uu____25197) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25191 in
                                                                    (uu____25177,
                                                                    [x],
                                                                    uu____25190) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25166 in
                                                                    let uu____25216
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25165,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25216) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25158
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25223
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
                                                                    (let uu____25251
                                                                    =
                                                                    let uu____25252
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25252
                                                                    dapp1 in
                                                                    [uu____25251]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25223
                                                                    FStar_List.flatten in
                                                                    let uu____25259
                                                                    =
                                                                    let uu____25266
                                                                    =
                                                                    let uu____25267
                                                                    =
                                                                    let uu____25278
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25289
                                                                    =
                                                                    let uu____25290
                                                                    =
                                                                    let uu____25295
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25295) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25290 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25278,
                                                                    uu____25289) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25267 in
                                                                    (uu____25266,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25259) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25316 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25316
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
                                                                 | uu____25359
                                                                    ->
                                                                    let uu____25360
                                                                    =
                                                                    let uu____25361
                                                                    =
                                                                    let uu____25366
                                                                    =
                                                                    let uu____25367
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25367 in
                                                                    (uu____25366,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25361 in
                                                                    FStar_Exn.raise
                                                                    uu____25360 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25383
                                                                    =
                                                                    let uu____25384
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25384 in
                                                                    if
                                                                    uu____25383
                                                                    then
                                                                    let uu____25397
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25397]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25399
                                                               =
                                                               let uu____25412
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25462
                                                                     ->
                                                                    fun
                                                                    uu____25463
                                                                     ->
                                                                    match 
                                                                    (uu____25462,
                                                                    uu____25463)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25558
                                                                    =
                                                                    let uu____25565
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25565 in
                                                                    (match uu____25558
                                                                    with
                                                                    | 
                                                                    (uu____25578,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25586
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25586
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25588
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25588
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
                                                                 uu____25412 in
                                                             (match uu____25399
                                                              with
                                                              | (uu____25603,arg_vars,elim_eqns_or_guards,uu____25606)
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
                                                                    let uu____25636
                                                                    =
                                                                    let uu____25643
                                                                    =
                                                                    let uu____25644
                                                                    =
                                                                    let uu____25655
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25666
                                                                    =
                                                                    let uu____25667
                                                                    =
                                                                    let uu____25672
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25672) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25667 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25655,
                                                                    uu____25666) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25644 in
                                                                    (uu____25643,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25636 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25695
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25695,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25697
                                                                    =
                                                                    let uu____25704
                                                                    =
                                                                    let uu____25705
                                                                    =
                                                                    let uu____25716
                                                                    =
                                                                    let uu____25721
                                                                    =
                                                                    let uu____25724
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25724] in
                                                                    [uu____25721] in
                                                                    let uu____25729
                                                                    =
                                                                    let uu____25730
                                                                    =
                                                                    let uu____25735
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25736
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25735,
                                                                    uu____25736) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25730 in
                                                                    (uu____25716,
                                                                    [x],
                                                                    uu____25729) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25705 in
                                                                    let uu____25755
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25704,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25755) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25697
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25762
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
                                                                    (let uu____25790
                                                                    =
                                                                    let uu____25791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25791
                                                                    dapp1 in
                                                                    [uu____25790]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25762
                                                                    FStar_List.flatten in
                                                                    let uu____25798
                                                                    =
                                                                    let uu____25805
                                                                    =
                                                                    let uu____25806
                                                                    =
                                                                    let uu____25817
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25828
                                                                    =
                                                                    let uu____25829
                                                                    =
                                                                    let uu____25834
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25834) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25829 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25817,
                                                                    uu____25828) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25806 in
                                                                    (uu____25805,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25798) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25853 ->
                                                        ((let uu____25855 =
                                                            let uu____25856 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25857 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25856
                                                              uu____25857 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25855);
                                                         ([], []))) in
                                             let uu____25862 = encode_elim () in
                                             (match uu____25862 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25882 =
                                                      let uu____25885 =
                                                        let uu____25888 =
                                                          let uu____25891 =
                                                            let uu____25894 =
                                                              let uu____25895
                                                                =
                                                                let uu____25906
                                                                  =
                                                                  let uu____25909
                                                                    =
                                                                    let uu____25910
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25910 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25909 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25906) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25895 in
                                                            [uu____25894] in
                                                          let uu____25915 =
                                                            let uu____25918 =
                                                              let uu____25921
                                                                =
                                                                let uu____25924
                                                                  =
                                                                  let uu____25927
                                                                    =
                                                                    let uu____25930
                                                                    =
                                                                    let uu____25933
                                                                    =
                                                                    let uu____25934
                                                                    =
                                                                    let uu____25941
                                                                    =
                                                                    let uu____25942
                                                                    =
                                                                    let uu____25953
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25953) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25942 in
                                                                    (uu____25941,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25934 in
                                                                    let uu____25966
                                                                    =
                                                                    let uu____25969
                                                                    =
                                                                    let uu____25970
                                                                    =
                                                                    let uu____25977
                                                                    =
                                                                    let uu____25978
                                                                    =
                                                                    let uu____25989
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____26000
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25989,
                                                                    uu____26000) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25978 in
                                                                    (uu____25977,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25970 in
                                                                    [uu____25969] in
                                                                    uu____25933
                                                                    ::
                                                                    uu____25966 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25930 in
                                                                  FStar_List.append
                                                                    uu____25927
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25924 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25921 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25918 in
                                                          FStar_List.append
                                                            uu____25891
                                                            uu____25915 in
                                                        FStar_List.append
                                                          decls3 uu____25888 in
                                                      FStar_List.append
                                                        decls2 uu____25885 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25882 in
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
           (fun uu____26046  ->
              fun se  ->
                match uu____26046 with
                | (g,env1) ->
                    let uu____26066 = encode_sigelt env1 se in
                    (match uu____26066 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26125 =
        match uu____26125 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26157 ->
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
                 ((let uu____26163 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26163
                   then
                     let uu____26164 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26165 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26166 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26164 uu____26165 uu____26166
                   else ());
                  (let uu____26168 = encode_term t1 env1 in
                   match uu____26168 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26184 =
                         let uu____26191 =
                           let uu____26192 =
                             let uu____26193 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26193
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26192 in
                         new_term_constant_from_string env1 x uu____26191 in
                       (match uu____26184 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26209 = FStar_Options.log_queries () in
                              if uu____26209
                              then
                                let uu____26212 =
                                  let uu____26213 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26214 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26215 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26213 uu____26214 uu____26215 in
                                FStar_Pervasives_Native.Some uu____26212
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26231,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26245 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26245 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26268,se,uu____26270) ->
                 let uu____26275 = encode_sigelt env1 se in
                 (match uu____26275 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26292,se) ->
                 let uu____26298 = encode_sigelt env1 se in
                 (match uu____26298 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26315 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26315 with | (uu____26338,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26353 'Auu____26354 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26354,'Auu____26353)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26422  ->
              match uu____26422 with
              | (l,uu____26434,uu____26435) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26481  ->
              match uu____26481 with
              | (l,uu____26495,uu____26496) ->
                  let uu____26505 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26506 =
                    let uu____26509 =
                      let uu____26510 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26510 in
                    [uu____26509] in
                  uu____26505 :: uu____26506)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26532 =
      let uu____26535 =
        let uu____26536 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26539 =
          let uu____26540 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26540 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26536;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26539
        } in
      [uu____26535] in
    FStar_ST.op_Colon_Equals last_env uu____26532
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26567 = FStar_ST.op_Bang last_env in
      match uu____26567 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26589 ->
          let uu___161_26592 = e in
          let uu____26593 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_26592.bindings);
            depth = (uu___161_26592.depth);
            tcenv;
            warn = (uu___161_26592.warn);
            cache = (uu___161_26592.cache);
            nolabels = (uu___161_26592.nolabels);
            use_zfuel_name = (uu___161_26592.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_26592.encode_non_total_function_typ);
            current_module_name = uu____26593
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26598 = FStar_ST.op_Bang last_env in
    match uu____26598 with
    | [] -> failwith "Empty env stack"
    | uu____26619::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26644  ->
    let uu____26645 = FStar_ST.op_Bang last_env in
    match uu____26645 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_26674 = hd1 in
          {
            bindings = (uu___162_26674.bindings);
            depth = (uu___162_26674.depth);
            tcenv = (uu___162_26674.tcenv);
            warn = (uu___162_26674.warn);
            cache = refs;
            nolabels = (uu___162_26674.nolabels);
            use_zfuel_name = (uu___162_26674.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_26674.encode_non_total_function_typ);
            current_module_name = (uu___162_26674.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26696  ->
    let uu____26697 = FStar_ST.op_Bang last_env in
    match uu____26697 with
    | [] -> failwith "Popping an empty stack"
    | uu____26718::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____26743  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____26747  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____26751  ->
    let uu____26752 = FStar_ST.op_Bang last_env in
    match uu____26752 with
    | hd1::uu____26774::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26796 -> failwith "Impossible"
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
        | (uu____26861::uu____26862,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___163_26870 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___163_26870.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___163_26870.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___163_26870.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26871 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26888 =
        let uu____26891 =
          let uu____26892 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26892 in
        let uu____26893 = open_fact_db_tags env in uu____26891 :: uu____26893 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26888
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
      let uu____26917 = encode_sigelt env se in
      match uu____26917 with
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
        let uu____26955 = FStar_Options.log_queries () in
        if uu____26955
        then
          let uu____26958 =
            let uu____26959 =
              let uu____26960 =
                let uu____26961 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26961 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26960 in
            FStar_SMTEncoding_Term.Caption uu____26959 in
          uu____26958 :: decls
        else decls in
      let env =
        let uu____26972 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26972 tcenv in
      let uu____26973 = encode_top_level_facts env se in
      match uu____26973 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26987 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26987))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27001 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27001
       then
         let uu____27002 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27002
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27037  ->
                 fun se  ->
                   match uu____27037 with
                   | (g,env2) ->
                       let uu____27057 = encode_top_level_facts env2 se in
                       (match uu____27057 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27080 =
         encode_signature
           (let uu___164_27089 = env in
            {
              bindings = (uu___164_27089.bindings);
              depth = (uu___164_27089.depth);
              tcenv = (uu___164_27089.tcenv);
              warn = false;
              cache = (uu___164_27089.cache);
              nolabels = (uu___164_27089.nolabels);
              use_zfuel_name = (uu___164_27089.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___164_27089.encode_non_total_function_typ);
              current_module_name = (uu___164_27089.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27080 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27106 = FStar_Options.log_queries () in
             if uu____27106
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___165_27114 = env1 in
               {
                 bindings = (uu___165_27114.bindings);
                 depth = (uu___165_27114.depth);
                 tcenv = (uu___165_27114.tcenv);
                 warn = true;
                 cache = (uu___165_27114.cache);
                 nolabels = (uu___165_27114.nolabels);
                 use_zfuel_name = (uu___165_27114.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___165_27114.encode_non_total_function_typ);
                 current_module_name = (uu___165_27114.current_module_name)
               });
            (let uu____27116 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27116
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
        (let uu____27171 =
           let uu____27172 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27172.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27171);
        (let env =
           let uu____27174 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27174 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27186 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27221 = aux rest in
                 (match uu____27221 with
                  | (out,rest1) ->
                      let t =
                        let uu____27251 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27251 with
                        | FStar_Pervasives_Native.Some uu____27256 ->
                            let uu____27257 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27257
                              x.FStar_Syntax_Syntax.sort
                        | uu____27258 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27262 =
                        let uu____27265 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___166_27268 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_27268.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_27268.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27265 :: out in
                      (uu____27262, rest1))
             | uu____27273 -> ([], bindings1) in
           let uu____27280 = aux bindings in
           match uu____27280 with
           | (closing,bindings1) ->
               let uu____27305 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27305, bindings1) in
         match uu____27186 with
         | (q1,bindings1) ->
             let uu____27328 =
               let uu____27333 =
                 FStar_List.filter
                   (fun uu___131_27338  ->
                      match uu___131_27338 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27339 ->
                          false
                      | uu____27346 -> true) bindings1 in
               encode_env_bindings env uu____27333 in
             (match uu____27328 with
              | (env_decls,env1) ->
                  ((let uu____27364 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27364
                    then
                      let uu____27365 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27365
                    else ());
                   (let uu____27367 = encode_formula q1 env1 in
                    match uu____27367 with
                    | (phi,qdecls) ->
                        let uu____27388 =
                          let uu____27393 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27393 phi in
                        (match uu____27388 with
                         | (labels,phi1) ->
                             let uu____27410 = encode_labels labels in
                             (match uu____27410 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27447 =
                                      let uu____27454 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27455 =
                                        varops.mk_unique "@query" in
                                      (uu____27454,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27455) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27447 in
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
        let uu____27474 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27474 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27476 = encode_formula q env in
       match uu____27476 with
       | (f,uu____27482) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27484) -> true
             | uu____27489 -> false)))