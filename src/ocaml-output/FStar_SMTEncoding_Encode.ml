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
  mk_unique: Prims.string -> Prims.string;}
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
        let id = next_id1 () in
        let f =
          let uu____1476 = FStar_SMTEncoding_Util.mk_String_const id in
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
  FStar_Pervasives_Native.tuple4
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
  cache_symbol_assumption_names: Prims.string Prims.list;}
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
  current_module_name: Prims.string;}
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
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
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
        FStar_Pervasives_Native.tuple2 Prims.list;}
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
        let uu____4265 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____4265
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4267) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____4283) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4286 =
          let uu____4287 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____4287 in
        failwith uu____4286
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4308 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4321 ->
            let uu____4328 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4328
        | uu____4329 ->
            if norm1
            then let uu____4330 = whnf env t1 in aux false uu____4330
            else
              (let uu____4332 =
                 let uu____4333 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4334 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4333 uu____4334 in
               failwith uu____4332) in
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
    | uu____4366 ->
        let uu____4367 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4367)
let is_arithmetic_primitive:
  'Auu____4384 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4384 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4404::uu____4405::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4409::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4412 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4434 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4450 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4457 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4457)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4496)::uu____4497::uu____4498::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4549)::uu____4550::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4587 -> false
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
        (let uu____4796 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4796
         then
           let uu____4797 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4797
         else ());
        (let uu____4799 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4883  ->
                   fun b  ->
                     match uu____4883 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4962 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4978 = gen_term_var env1 x in
                           match uu____4978 with
                           | (xxsym,xx,env') ->
                               let uu____5002 =
                                 let uu____5007 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____5007 env1 xx in
                               (match uu____5002 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4962 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4799 with
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
          let uu____5166 = encode_term t env in
          match uu____5166 with
          | (t1,decls) ->
              let uu____5177 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____5177, decls)
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
          let uu____5188 = encode_term t env in
          match uu____5188 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5203 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____5203, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5205 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____5205, decls))
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
        let uu____5211 = encode_args args_e env in
        match uu____5211 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5230 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5239 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5239 in
            let binary arg_tms1 =
              let uu____5252 =
                let uu____5253 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5253 in
              let uu____5254 =
                let uu____5255 =
                  let uu____5256 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5256 in
                FStar_SMTEncoding_Term.unboxInt uu____5255 in
              (uu____5252, uu____5254) in
            let mk_default uu____5262 =
              let uu____5263 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5263 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5314 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5314
              then
                let uu____5315 = let uu____5316 = mk_args ts in op uu____5316 in
                FStar_All.pipe_right uu____5315 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5345 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5345
              then
                let uu____5346 = binary ts in
                match uu____5346 with
                | (t1,t2) ->
                    let uu____5353 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5353
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5357 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5357
                 then
                   let uu____5358 = op (binary ts) in
                   FStar_All.pipe_right uu____5358
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
            let uu____5489 =
              let uu____5498 =
                FStar_List.tryFind
                  (fun uu____5520  ->
                     match uu____5520 with
                     | (l,uu____5530) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5498 FStar_Util.must in
            (match uu____5489 with
             | (uu____5569,op) ->
                 let uu____5579 = op arg_tms in (uu____5579, decls))
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
        let uu____5587 = FStar_List.hd args_e in
        match uu____5587 with
        | (tm_sz,uu____5595) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5605 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5605 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5613 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5613);
                   t_decls) in
            let uu____5614 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5634::(sz_arg,uu____5636)::uu____5637::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5686 =
                    let uu____5689 = FStar_List.tail args_e in
                    FStar_List.tail uu____5689 in
                  let uu____5692 =
                    let uu____5695 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5695 in
                  (uu____5686, uu____5692)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5701::(sz_arg,uu____5703)::uu____5704::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5753 =
                    let uu____5754 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5754 in
                  failwith uu____5753
              | uu____5763 ->
                  let uu____5770 = FStar_List.tail args_e in
                  (uu____5770, FStar_Pervasives_Native.None) in
            (match uu____5614 with
             | (arg_tms,ext_sz) ->
                 let uu____5793 = encode_args arg_tms env in
                 (match uu____5793 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5814 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5823 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5823 in
                      let unary_arith arg_tms2 =
                        let uu____5832 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5832 in
                      let binary arg_tms2 =
                        let uu____5845 =
                          let uu____5846 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5846 in
                        let uu____5847 =
                          let uu____5848 =
                            let uu____5849 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5849 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5848 in
                        (uu____5845, uu____5847) in
                      let binary_arith arg_tms2 =
                        let uu____5864 =
                          let uu____5865 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5865 in
                        let uu____5866 =
                          let uu____5867 =
                            let uu____5868 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5868 in
                          FStar_SMTEncoding_Term.unboxInt uu____5867 in
                        (uu____5864, uu____5866) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5917 =
                          let uu____5918 = mk_args ts in op uu____5918 in
                        FStar_All.pipe_right uu____5917 resBox in
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
                        let uu____6008 =
                          let uu____6011 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____6011 in
                        let uu____6013 =
                          let uu____6016 =
                            let uu____6017 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____6017 in
                          FStar_SMTEncoding_Term.boxBitVec uu____6016 in
                        mk_bv uu____6008 unary uu____6013 arg_tms2 in
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
                      let uu____6192 =
                        let uu____6201 =
                          FStar_List.tryFind
                            (fun uu____6223  ->
                               match uu____6223 with
                               | (l,uu____6233) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6201 FStar_Util.must in
                      (match uu____6192 with
                       | (uu____6274,op) ->
                           let uu____6284 = op arg_tms1 in
                           (uu____6284, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6295 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6295
       then
         let uu____6296 = FStar_Syntax_Print.tag_of_term t in
         let uu____6297 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6298 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6296 uu____6297
           uu____6298
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6304 ->
           let uu____6329 =
             let uu____6330 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6331 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6332 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6333 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6330
               uu____6331 uu____6332 uu____6333 in
           failwith uu____6329
       | FStar_Syntax_Syntax.Tm_unknown  ->
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
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6348 =
             let uu____6349 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6349 in
           failwith uu____6348
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6356) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6398) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6408 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6408, [])
       | FStar_Syntax_Syntax.Tm_type uu____6411 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6415) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6421 = encode_const c in (uu____6421, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6443 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6443 with
            | (binders1,res) ->
                let uu____6454 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6454
                then
                  let uu____6459 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6459 with
                   | (vars,guards,env',decls,uu____6484) ->
                       let fsym =
                         let uu____6502 = varops.fresh "f" in
                         (uu____6502, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6505 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_6514 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_6514.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_6514.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_6514.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_6514.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_6514.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_6514.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_6514.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_6514.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_6514.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_6514.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_6514.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_6514.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_6514.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_6514.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_6514.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_6514.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_6514.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_6514.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_6514.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___141_6514.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___141_6514.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_6514.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_6514.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_6514.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_6514.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___141_6514.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___141_6514.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___141_6514.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___141_6514.FStar_TypeChecker_Env.identifier_info)
                            }) res in
                       (match uu____6505 with
                        | (pre_opt,res_t) ->
                            let uu____6525 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6525 with
                             | (res_pred,decls') ->
                                 let uu____6536 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6549 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6549, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6553 =
                                         encode_formula pre env' in
                                       (match uu____6553 with
                                        | (guard,decls0) ->
                                            let uu____6566 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6566, decls0)) in
                                 (match uu____6536 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6578 =
                                          let uu____6589 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6589) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6578 in
                                      let cvars =
                                        let uu____6607 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6607
                                          (FStar_List.filter
                                             (fun uu____6621  ->
                                                match uu____6621 with
                                                | (x,uu____6627) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6646 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6646 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6654 =
                                             let uu____6655 =
                                               let uu____6662 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6662) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6655 in
                                           (uu____6654,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6682 =
                                               let uu____6683 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6683 in
                                             varops.mk_unique uu____6682 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6694 =
                                               FStar_Options.log_queries () in
                                             if uu____6694
                                             then
                                               let uu____6697 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6697
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6705 =
                                               let uu____6712 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6712) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6705 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6724 =
                                               let uu____6731 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6731,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6724 in
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
                                             let uu____6752 =
                                               let uu____6759 =
                                                 let uu____6760 =
                                                   let uu____6771 =
                                                     let uu____6772 =
                                                       let uu____6777 =
                                                         let uu____6778 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6778 in
                                                       (f_has_t, uu____6777) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6772 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6771) in
                                                 mkForall_fuel uu____6760 in
                                               (uu____6759,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6752 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6801 =
                                               let uu____6808 =
                                                 let uu____6809 =
                                                   let uu____6820 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6820) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6809 in
                                               (uu____6808,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6801 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6845 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6845);
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
                     let uu____6860 =
                       let uu____6867 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6867,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6860 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6879 =
                       let uu____6886 =
                         let uu____6887 =
                           let uu____6898 =
                             let uu____6899 =
                               let uu____6904 =
                                 let uu____6905 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6905 in
                               (f_has_t, uu____6904) in
                             FStar_SMTEncoding_Util.mkImp uu____6899 in
                           ([[f_has_t]], [fsym], uu____6898) in
                         mkForall_fuel uu____6887 in
                       (uu____6886, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6879 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6932 ->
           let uu____6939 =
             let uu____6944 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6944 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6951;
                 FStar_Syntax_Syntax.vars = uu____6952;_} ->
                 let uu____6959 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6959 with
                  | (b,f1) ->
                      let uu____6984 =
                        let uu____6985 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6985 in
                      (uu____6984, f1))
             | uu____6994 -> failwith "impossible" in
           (match uu____6939 with
            | (x,f) ->
                let uu____7005 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____7005 with
                 | (base_t,decls) ->
                     let uu____7016 = gen_term_var env x in
                     (match uu____7016 with
                      | (x1,xtm,env') ->
                          let uu____7030 = encode_formula f env' in
                          (match uu____7030 with
                           | (refinement,decls') ->
                               let uu____7041 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____7041 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____7057 =
                                        let uu____7060 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____7067 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____7060
                                          uu____7067 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7057 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7100  ->
                                              match uu____7100 with
                                              | (y,uu____7106) ->
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
                                    let uu____7139 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7139 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7147 =
                                           let uu____7148 =
                                             let uu____7155 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7155) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7148 in
                                         (uu____7147,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7176 =
                                             let uu____7177 =
                                               let uu____7178 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7178 in
                                             Prims.strcat module_name
                                               uu____7177 in
                                           varops.mk_unique uu____7176 in
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
                                           let uu____7192 =
                                             let uu____7199 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7199) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7192 in
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
                                           let uu____7214 =
                                             let uu____7221 =
                                               let uu____7222 =
                                                 let uu____7233 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7233) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7222 in
                                             (uu____7221,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7214 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7259 =
                                             let uu____7266 =
                                               let uu____7267 =
                                                 let uu____7278 =
                                                   let uu____7279 =
                                                     let uu____7284 =
                                                       let uu____7285 =
                                                         let uu____7296 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7296) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7285 in
                                                     (uu____7284, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7279 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7278) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7267 in
                                             (uu____7266,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7259 in
                                         let t_kinding =
                                           let uu____7334 =
                                             let uu____7341 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7341,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7334 in
                                         let t_interp =
                                           let uu____7359 =
                                             let uu____7366 =
                                               let uu____7367 =
                                                 let uu____7378 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7378) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7367 in
                                             let uu____7401 =
                                               let uu____7404 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7404 in
                                             (uu____7366, uu____7401,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7359 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7411 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7411);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7441 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7441 in
           let uu____7442 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7442 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7454 =
                    let uu____7461 =
                      let uu____7462 =
                        let uu____7463 =
                          let uu____7464 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7464 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7463 in
                      varops.mk_unique uu____7462 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7461) in
                  FStar_SMTEncoding_Util.mkAssume uu____7454 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7469 ->
           let uu____7484 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7484 with
            | (head1,args_e) ->
                let uu____7525 =
                  let uu____7538 =
                    let uu____7539 = FStar_Syntax_Subst.compress head1 in
                    uu____7539.FStar_Syntax_Syntax.n in
                  (uu____7538, args_e) in
                (match uu____7525 with
                 | uu____7554 when head_redex env head1 ->
                     let uu____7567 = whnf env t in
                     encode_term uu____7567 env
                 | uu____7568 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7587 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7601;
                       FStar_Syntax_Syntax.vars = uu____7602;_},uu____7603),uu____7604::
                    (v1,uu____7606)::(v2,uu____7608)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7659 = encode_term v1 env in
                     (match uu____7659 with
                      | (v11,decls1) ->
                          let uu____7670 = encode_term v2 env in
                          (match uu____7670 with
                           | (v21,decls2) ->
                               let uu____7681 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7681,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7685::(v1,uu____7687)::(v2,uu____7689)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7736 = encode_term v1 env in
                     (match uu____7736 with
                      | (v11,decls1) ->
                          let uu____7747 = encode_term v2 env in
                          (match uu____7747 with
                           | (v21,decls2) ->
                               let uu____7758 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7758,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7761) ->
                     let e0 =
                       let uu____7779 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7779 in
                     ((let uu____7787 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7787
                       then
                         let uu____7788 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7788
                       else ());
                      (let e =
                         let uu____7793 =
                           let uu____7794 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7795 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7794
                             uu____7795 in
                         uu____7793 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7804),(arg,uu____7806)::[]) -> encode_term arg env
                 | uu____7831 ->
                     let uu____7844 = encode_args args_e env in
                     (match uu____7844 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7899 = encode_term head1 env in
                            match uu____7899 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7963 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7963 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8041  ->
                                                 fun uu____8042  ->
                                                   match (uu____8041,
                                                           uu____8042)
                                                   with
                                                   | ((bv,uu____8064),
                                                      (a,uu____8066)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____8084 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____8084
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____8089 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____8089 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____8104 =
                                                   let uu____8111 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____8120 =
                                                     let uu____8121 =
                                                       let uu____8122 =
                                                         let uu____8123 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____8123 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8122 in
                                                     varops.mk_unique
                                                       uu____8121 in
                                                   (uu____8111,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8120) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8104 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8140 = lookup_free_var_sym env fv in
                            match uu____8140 with
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
                                   FStar_Syntax_Syntax.pos = uu____8171;
                                   FStar_Syntax_Syntax.vars = uu____8172;_},uu____8173)
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
                                   FStar_Syntax_Syntax.pos = uu____8184;
                                   FStar_Syntax_Syntax.vars = uu____8185;_},uu____8186)
                                ->
                                let uu____8191 =
                                  let uu____8192 =
                                    let uu____8197 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8197
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8192
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8191
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8227 =
                                  let uu____8228 =
                                    let uu____8233 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8233
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8228
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8227
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8262,(FStar_Util.Inl t1,uu____8264),uu____8265)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8314,(FStar_Util.Inr c,uu____8316),uu____8317)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8366 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8393 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8393 in
                               let uu____8394 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8394 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8410;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8411;_},uu____8412)
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
                                     | uu____8426 ->
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
           let uu____8475 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8475 with
            | (bs1,body1,opening) ->
                let fallback uu____8498 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8505 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8505, [decl]) in
                let is_impure rc =
                  let uu____8512 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8512 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8522 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8522
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8542 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8542
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8546 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8546)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8553 =
                         let uu____8554 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8554 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8553);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8556 =
                       (is_impure rc) &&
                         (let uu____8558 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8558) in
                     if uu____8556
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8565 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8565 with
                        | (vars,guards,envbody,decls,uu____8590) ->
                            let body2 =
                              let uu____8604 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8604
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8606 = encode_term body2 envbody in
                            (match uu____8606 with
                             | (body3,decls') ->
                                 let uu____8617 =
                                   let uu____8626 = codomain_eff rc in
                                   match uu____8626 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8645 = encode_term tfun env in
                                       (match uu____8645 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8617 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8677 =
                                          let uu____8688 =
                                            let uu____8689 =
                                              let uu____8694 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8694, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8689 in
                                          ([], vars, uu____8688) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8677 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8706 =
                                              let uu____8709 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8709
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8706 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8728 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8728 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8736 =
                                             let uu____8737 =
                                               let uu____8744 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8744) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8737 in
                                           (uu____8736,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8755 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8755 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8766 =
                                                    let uu____8767 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8767 = cache_size in
                                                  if uu____8766
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
                                                    let uu____8783 =
                                                      let uu____8784 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8784 in
                                                    varops.mk_unique
                                                      uu____8783 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8791 =
                                                    let uu____8798 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8798) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8791 in
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
                                                      let uu____8816 =
                                                        let uu____8817 =
                                                          let uu____8824 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8824,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8817 in
                                                      [uu____8816] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8837 =
                                                    let uu____8844 =
                                                      let uu____8845 =
                                                        let uu____8856 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8856) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8845 in
                                                    (uu____8844,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8837 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8873 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8873);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8876,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8877;
                          FStar_Syntax_Syntax.lbunivs = uu____8878;
                          FStar_Syntax_Syntax.lbtyp = uu____8879;
                          FStar_Syntax_Syntax.lbeff = uu____8880;
                          FStar_Syntax_Syntax.lbdef = uu____8881;_}::uu____8882),uu____8883)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8909;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8911;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8932 ->
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
              let uu____9002 = encode_term e1 env in
              match uu____9002 with
              | (ee1,decls1) ->
                  let uu____9013 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9013 with
                   | (xs,e21) ->
                       let uu____9038 = FStar_List.hd xs in
                       (match uu____9038 with
                        | (x1,uu____9052) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9054 = encode_body e21 env' in
                            (match uu____9054 with
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
            let uu____9086 =
              let uu____9093 =
                let uu____9094 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9094 in
              gen_term_var env uu____9093 in
            match uu____9086 with
            | (scrsym,scr',env1) ->
                let uu____9102 = encode_term e env1 in
                (match uu____9102 with
                 | (scr,decls) ->
                     let uu____9113 =
                       let encode_branch b uu____9138 =
                         match uu____9138 with
                         | (else_case,decls1) ->
                             let uu____9157 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9157 with
                              | (p,w,br) ->
                                  let uu____9183 = encode_pat env1 p in
                                  (match uu____9183 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9220  ->
                                                   match uu____9220 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9227 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9249 =
                                               encode_term w1 env2 in
                                             (match uu____9249 with
                                              | (w2,decls2) ->
                                                  let uu____9262 =
                                                    let uu____9263 =
                                                      let uu____9268 =
                                                        let uu____9269 =
                                                          let uu____9274 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9274) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9269 in
                                                      (guard, uu____9268) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9263 in
                                                  (uu____9262, decls2)) in
                                       (match uu____9227 with
                                        | (guard1,decls2) ->
                                            let uu____9287 =
                                              encode_br br env2 in
                                            (match uu____9287 with
                                             | (br1,decls3) ->
                                                 let uu____9300 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9300,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9113 with
                      | (match_tm,decls1) ->
                          let uu____9319 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9319, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9359 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9359
       then
         let uu____9360 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9360
       else ());
      (let uu____9362 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9362 with
       | (vars,pat_term) ->
           let uu____9379 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9432  ->
                     fun v1  ->
                       match uu____9432 with
                       | (env1,vars1) ->
                           let uu____9484 = gen_term_var env1 v1 in
                           (match uu____9484 with
                            | (xx,uu____9506,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9379 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9585 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9586 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9587 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9595 =
                        let uu____9600 = encode_const c in
                        (scrutinee, uu____9600) in
                      FStar_SMTEncoding_Util.mkEq uu____9595
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9621 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9621 with
                        | (uu____9628,uu____9629::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9632 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9665  ->
                                  match uu____9665 with
                                  | (arg,uu____9673) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9679 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9679)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9706) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9737 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9760 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9804  ->
                                  match uu____9804 with
                                  | (arg,uu____9818) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9824 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9824)) in
                      FStar_All.pipe_right uu____9760 FStar_List.flatten in
                let pat_term1 uu____9852 = encode_term pat_term env1 in
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
      let uu____9862 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9900  ->
                fun uu____9901  ->
                  match (uu____9900, uu____9901) with
                  | ((tms,decls),(t,uu____9937)) ->
                      let uu____9958 = encode_term t env in
                      (match uu____9958 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9862 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10015 = FStar_Syntax_Util.list_elements e in
        match uu____10015 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____10036 =
          let uu____10051 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10051 FStar_Syntax_Util.head_and_args in
        match uu____10036 with
        | (head1,args) ->
            let uu____10090 =
              let uu____10103 =
                let uu____10104 = FStar_Syntax_Util.un_uinst head1 in
                uu____10104.FStar_Syntax_Syntax.n in
              (uu____10103, args) in
            (match uu____10090 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10118,uu____10119)::(e,uu____10121)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10156 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10192 =
            let uu____10207 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10207 FStar_Syntax_Util.head_and_args in
          match uu____10192 with
          | (head1,args) ->
              let uu____10248 =
                let uu____10261 =
                  let uu____10262 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10262.FStar_Syntax_Syntax.n in
                (uu____10261, args) in
              (match uu____10248 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10279)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10306 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10328 = smt_pat_or1 t1 in
            (match uu____10328 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10344 = list_elements1 e in
                 FStar_All.pipe_right uu____10344
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10362 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10362
                           (FStar_List.map one_pat)))
             | uu____10373 ->
                 let uu____10378 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10378])
        | uu____10399 ->
            let uu____10402 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10402] in
      let uu____10423 =
        let uu____10442 =
          let uu____10443 = FStar_Syntax_Subst.compress t in
          uu____10443.FStar_Syntax_Syntax.n in
        match uu____10442 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10482 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10482 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10525;
                        FStar_Syntax_Syntax.effect_name = uu____10526;
                        FStar_Syntax_Syntax.result_typ = uu____10527;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10529)::(post,uu____10531)::(pats,uu____10533)::[];
                        FStar_Syntax_Syntax.flags = uu____10534;_}
                      ->
                      let uu____10575 = lemma_pats pats in
                      (binders1, pre, post, uu____10575)
                  | uu____10592 -> failwith "impos"))
        | uu____10611 -> failwith "Impos" in
      match uu____10423 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___142_10659 = env in
            {
              bindings = (uu___142_10659.bindings);
              depth = (uu___142_10659.depth);
              tcenv = (uu___142_10659.tcenv);
              warn = (uu___142_10659.warn);
              cache = (uu___142_10659.cache);
              nolabels = (uu___142_10659.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___142_10659.encode_non_total_function_typ);
              current_module_name = (uu___142_10659.current_module_name)
            } in
          let uu____10660 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10660 with
           | (vars,guards,env2,decls,uu____10685) ->
               let uu____10698 =
                 let uu____10711 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10755 =
                             let uu____10764 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10764
                               FStar_List.unzip in
                           match uu____10755 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10711 FStar_List.unzip in
               (match uu____10698 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___143_10873 = env2 in
                      {
                        bindings = (uu___143_10873.bindings);
                        depth = (uu___143_10873.depth);
                        tcenv = (uu___143_10873.tcenv);
                        warn = (uu___143_10873.warn);
                        cache = (uu___143_10873.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___143_10873.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___143_10873.encode_non_total_function_typ);
                        current_module_name =
                          (uu___143_10873.current_module_name)
                      } in
                    let uu____10874 =
                      let uu____10879 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10879 env3 in
                    (match uu____10874 with
                     | (pre1,decls'') ->
                         let uu____10886 =
                           let uu____10891 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10891 env3 in
                         (match uu____10886 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10901 =
                                let uu____10902 =
                                  let uu____10913 =
                                    let uu____10914 =
                                      let uu____10919 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10919, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10914 in
                                  (pats, vars, uu____10913) in
                                FStar_SMTEncoding_Util.mkForall uu____10902 in
                              (uu____10901, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10938 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10938
        then
          let uu____10939 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10940 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10939 uu____10940
        else () in
      let enc f r l =
        let uu____10973 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11001 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11001 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10973 with
        | (decls,args) ->
            let uu____11030 =
              let uu___144_11031 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_11031.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_11031.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11030, decls) in
      let const_op f r uu____11062 =
        let uu____11075 = f r in (uu____11075, []) in
      let un_op f l =
        let uu____11094 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11094 in
      let bin_op f uu___118_11110 =
        match uu___118_11110 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11121 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11155 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11178  ->
                 match uu____11178 with
                 | (t,uu____11192) ->
                     let uu____11193 = encode_formula t env in
                     (match uu____11193 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11155 with
        | (decls,phis) ->
            let uu____11222 =
              let uu___145_11223 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_11223.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_11223.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11222, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11284  ->
               match uu____11284 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11303) -> false
                    | uu____11304 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11319 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11319
        else
          (let uu____11333 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11333 r rf) in
      let mk_imp1 r uu___119_11358 =
        match uu___119_11358 with
        | (lhs,uu____11364)::(rhs,uu____11366)::[] ->
            let uu____11393 = encode_formula rhs env in
            (match uu____11393 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11408) ->
                      (l1, decls1)
                  | uu____11413 ->
                      let uu____11414 = encode_formula lhs env in
                      (match uu____11414 with
                       | (l2,decls2) ->
                           let uu____11425 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11425, (FStar_List.append decls1 decls2)))))
        | uu____11428 -> failwith "impossible" in
      let mk_ite r uu___120_11449 =
        match uu___120_11449 with
        | (guard,uu____11455)::(_then,uu____11457)::(_else,uu____11459)::[]
            ->
            let uu____11496 = encode_formula guard env in
            (match uu____11496 with
             | (g,decls1) ->
                 let uu____11507 = encode_formula _then env in
                 (match uu____11507 with
                  | (t,decls2) ->
                      let uu____11518 = encode_formula _else env in
                      (match uu____11518 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11532 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11557 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11557 in
      let connectives =
        let uu____11575 =
          let uu____11588 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11588) in
        let uu____11605 =
          let uu____11620 =
            let uu____11633 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11633) in
          let uu____11650 =
            let uu____11665 =
              let uu____11680 =
                let uu____11693 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11693) in
              let uu____11710 =
                let uu____11725 =
                  let uu____11740 =
                    let uu____11753 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11753) in
                  [uu____11740;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11725 in
              uu____11680 :: uu____11710 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11665 in
          uu____11620 :: uu____11650 in
        uu____11575 :: uu____11605 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12074 = encode_formula phi' env in
            (match uu____12074 with
             | (phi2,decls) ->
                 let uu____12085 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12085, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12086 ->
            let uu____12093 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12093 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12132 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12132 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12144;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12146;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12167 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12167 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12214::(x,uu____12216)::(t,uu____12218)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12265 = encode_term x env in
                 (match uu____12265 with
                  | (x1,decls) ->
                      let uu____12276 = encode_term t env in
                      (match uu____12276 with
                       | (t1,decls') ->
                           let uu____12287 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12287, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12292)::(msg,uu____12294)::(phi2,uu____12296)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12341 =
                   let uu____12346 =
                     let uu____12347 = FStar_Syntax_Subst.compress r in
                     uu____12347.FStar_Syntax_Syntax.n in
                   let uu____12350 =
                     let uu____12351 = FStar_Syntax_Subst.compress msg in
                     uu____12351.FStar_Syntax_Syntax.n in
                   (uu____12346, uu____12350) in
                 (match uu____12341 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12360))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12366 -> fallback phi2)
             | uu____12371 when head_redex env head2 ->
                 let uu____12384 = whnf env phi1 in
                 encode_formula uu____12384 env
             | uu____12385 ->
                 let uu____12398 = encode_term phi1 env in
                 (match uu____12398 with
                  | (tt,decls) ->
                      let uu____12409 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___146_12412 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___146_12412.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___146_12412.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12409, decls)))
        | uu____12413 ->
            let uu____12414 = encode_term phi1 env in
            (match uu____12414 with
             | (tt,decls) ->
                 let uu____12425 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___147_12428 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___147_12428.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___147_12428.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12425, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12464 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12464 with
        | (vars,guards,env2,decls,uu____12503) ->
            let uu____12516 =
              let uu____12529 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12577 =
                          let uu____12586 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12616  ->
                                    match uu____12616 with
                                    | (t,uu____12626) ->
                                        encode_term t
                                          (let uu___148_12628 = env2 in
                                           {
                                             bindings =
                                               (uu___148_12628.bindings);
                                             depth = (uu___148_12628.depth);
                                             tcenv = (uu___148_12628.tcenv);
                                             warn = (uu___148_12628.warn);
                                             cache = (uu___148_12628.cache);
                                             nolabels =
                                               (uu___148_12628.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___148_12628.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___148_12628.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12586 FStar_List.unzip in
                        match uu____12577 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12529 FStar_List.unzip in
            (match uu____12516 with
             | (pats,decls') ->
                 let uu____12727 = encode_formula body env2 in
                 (match uu____12727 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12759;
                             FStar_SMTEncoding_Term.rng = uu____12760;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12775 -> guards in
                      let uu____12780 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12780, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12840  ->
                   match uu____12840 with
                   | (x,uu____12846) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12854 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12866 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12866) uu____12854 tl1 in
             let uu____12869 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12896  ->
                       match uu____12896 with
                       | (b,uu____12902) ->
                           let uu____12903 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12903)) in
             (match uu____12869 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12909) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12923 =
                    let uu____12924 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12924 in
                  FStar_Errors.warn pos uu____12923) in
       let uu____12925 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12925 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12934 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12992  ->
                     match uu____12992 with
                     | (l,uu____13006) -> FStar_Ident.lid_equals op l)) in
           (match uu____12934 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13039,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13079 = encode_q_body env vars pats body in
             match uu____13079 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13124 =
                     let uu____13135 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13135) in
                   FStar_SMTEncoding_Term.mkForall uu____13124
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13154 = encode_q_body env vars pats body in
             match uu____13154 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13198 =
                   let uu____13199 =
                     let uu____13210 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13210) in
                   FStar_SMTEncoding_Term.mkExists uu____13199
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13198, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}
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
  let uu____13308 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13308 with
  | (asym,a) ->
      let uu____13315 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13315 with
       | (xsym,x) ->
           let uu____13322 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13322 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13366 =
                      let uu____13377 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13377, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13366 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13403 =
                      let uu____13410 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13410) in
                    FStar_SMTEncoding_Util.mkApp uu____13403 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13423 =
                    let uu____13426 =
                      let uu____13429 =
                        let uu____13432 =
                          let uu____13433 =
                            let uu____13440 =
                              let uu____13441 =
                                let uu____13452 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13452) in
                              FStar_SMTEncoding_Util.mkForall uu____13441 in
                            (uu____13440, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13433 in
                        let uu____13469 =
                          let uu____13472 =
                            let uu____13473 =
                              let uu____13480 =
                                let uu____13481 =
                                  let uu____13492 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13492) in
                                FStar_SMTEncoding_Util.mkForall uu____13481 in
                              (uu____13480,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13473 in
                          [uu____13472] in
                        uu____13432 :: uu____13469 in
                      xtok_decl :: uu____13429 in
                    xname_decl :: uu____13426 in
                  (xtok1, uu____13423) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13583 =
                    let uu____13596 =
                      let uu____13605 =
                        let uu____13606 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13606 in
                      quant axy uu____13605 in
                    (FStar_Parser_Const.op_Eq, uu____13596) in
                  let uu____13615 =
                    let uu____13630 =
                      let uu____13643 =
                        let uu____13652 =
                          let uu____13653 =
                            let uu____13654 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13654 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13653 in
                        quant axy uu____13652 in
                      (FStar_Parser_Const.op_notEq, uu____13643) in
                    let uu____13663 =
                      let uu____13678 =
                        let uu____13691 =
                          let uu____13700 =
                            let uu____13701 =
                              let uu____13702 =
                                let uu____13707 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13708 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13707, uu____13708) in
                              FStar_SMTEncoding_Util.mkLT uu____13702 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13701 in
                          quant xy uu____13700 in
                        (FStar_Parser_Const.op_LT, uu____13691) in
                      let uu____13717 =
                        let uu____13732 =
                          let uu____13745 =
                            let uu____13754 =
                              let uu____13755 =
                                let uu____13756 =
                                  let uu____13761 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13762 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13761, uu____13762) in
                                FStar_SMTEncoding_Util.mkLTE uu____13756 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13755 in
                            quant xy uu____13754 in
                          (FStar_Parser_Const.op_LTE, uu____13745) in
                        let uu____13771 =
                          let uu____13786 =
                            let uu____13799 =
                              let uu____13808 =
                                let uu____13809 =
                                  let uu____13810 =
                                    let uu____13815 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13816 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13815, uu____13816) in
                                  FStar_SMTEncoding_Util.mkGT uu____13810 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13809 in
                              quant xy uu____13808 in
                            (FStar_Parser_Const.op_GT, uu____13799) in
                          let uu____13825 =
                            let uu____13840 =
                              let uu____13853 =
                                let uu____13862 =
                                  let uu____13863 =
                                    let uu____13864 =
                                      let uu____13869 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13870 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13869, uu____13870) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13864 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13863 in
                                quant xy uu____13862 in
                              (FStar_Parser_Const.op_GTE, uu____13853) in
                            let uu____13879 =
                              let uu____13894 =
                                let uu____13907 =
                                  let uu____13916 =
                                    let uu____13917 =
                                      let uu____13918 =
                                        let uu____13923 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13924 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13923, uu____13924) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13918 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13917 in
                                  quant xy uu____13916 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13907) in
                              let uu____13933 =
                                let uu____13948 =
                                  let uu____13961 =
                                    let uu____13970 =
                                      let uu____13971 =
                                        let uu____13972 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13972 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13971 in
                                    quant qx uu____13970 in
                                  (FStar_Parser_Const.op_Minus, uu____13961) in
                                let uu____13981 =
                                  let uu____13996 =
                                    let uu____14009 =
                                      let uu____14018 =
                                        let uu____14019 =
                                          let uu____14020 =
                                            let uu____14025 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14026 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14025, uu____14026) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14020 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14019 in
                                      quant xy uu____14018 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14009) in
                                  let uu____14035 =
                                    let uu____14050 =
                                      let uu____14063 =
                                        let uu____14072 =
                                          let uu____14073 =
                                            let uu____14074 =
                                              let uu____14079 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14080 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14079, uu____14080) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14074 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14073 in
                                        quant xy uu____14072 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14063) in
                                    let uu____14089 =
                                      let uu____14104 =
                                        let uu____14117 =
                                          let uu____14126 =
                                            let uu____14127 =
                                              let uu____14128 =
                                                let uu____14133 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14134 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14133, uu____14134) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14128 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14127 in
                                          quant xy uu____14126 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14117) in
                                      let uu____14143 =
                                        let uu____14158 =
                                          let uu____14171 =
                                            let uu____14180 =
                                              let uu____14181 =
                                                let uu____14182 =
                                                  let uu____14187 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14188 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14187, uu____14188) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14182 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14181 in
                                            quant xy uu____14180 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14171) in
                                        let uu____14197 =
                                          let uu____14212 =
                                            let uu____14225 =
                                              let uu____14234 =
                                                let uu____14235 =
                                                  let uu____14236 =
                                                    let uu____14241 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14242 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14241,
                                                      uu____14242) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14236 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14235 in
                                              quant xy uu____14234 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14225) in
                                          let uu____14251 =
                                            let uu____14266 =
                                              let uu____14279 =
                                                let uu____14288 =
                                                  let uu____14289 =
                                                    let uu____14290 =
                                                      let uu____14295 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14296 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14295,
                                                        uu____14296) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14290 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14289 in
                                                quant xy uu____14288 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14279) in
                                            let uu____14305 =
                                              let uu____14320 =
                                                let uu____14333 =
                                                  let uu____14342 =
                                                    let uu____14343 =
                                                      let uu____14344 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14344 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14343 in
                                                  quant qx uu____14342 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14333) in
                                              [uu____14320] in
                                            uu____14266 :: uu____14305 in
                                          uu____14212 :: uu____14251 in
                                        uu____14158 :: uu____14197 in
                                      uu____14104 :: uu____14143 in
                                    uu____14050 :: uu____14089 in
                                  uu____13996 :: uu____14035 in
                                uu____13948 :: uu____13981 in
                              uu____13894 :: uu____13933 in
                            uu____13840 :: uu____13879 in
                          uu____13786 :: uu____13825 in
                        uu____13732 :: uu____13771 in
                      uu____13678 :: uu____13717 in
                    uu____13630 :: uu____13663 in
                  uu____13583 :: uu____13615 in
                let mk1 l v1 =
                  let uu____14558 =
                    let uu____14567 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14625  ->
                              match uu____14625 with
                              | (l',uu____14639) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14567
                      (FStar_Option.map
                         (fun uu____14699  ->
                            match uu____14699 with | (uu____14718,b) -> b v1)) in
                  FStar_All.pipe_right uu____14558 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14789  ->
                          match uu____14789 with
                          | (l',uu____14803) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14844 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14844 with
        | (xxsym,xx) ->
            let uu____14851 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14851 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14861 =
                   let uu____14868 =
                     let uu____14869 =
                       let uu____14880 =
                         let uu____14881 =
                           let uu____14886 =
                             let uu____14887 =
                               let uu____14892 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14892) in
                             FStar_SMTEncoding_Util.mkEq uu____14887 in
                           (xx_has_type, uu____14886) in
                         FStar_SMTEncoding_Util.mkImp uu____14881 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14880) in
                     FStar_SMTEncoding_Util.mkForall uu____14869 in
                   let uu____14917 =
                     let uu____14918 =
                       let uu____14919 =
                         let uu____14920 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14920 in
                       Prims.strcat module_name uu____14919 in
                     varops.mk_unique uu____14918 in
                   (uu____14868, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14917) in
                 FStar_SMTEncoding_Util.mkAssume uu____14861)
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
    let uu____14960 =
      let uu____14961 =
        let uu____14968 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14968, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14961 in
    let uu____14971 =
      let uu____14974 =
        let uu____14975 =
          let uu____14982 =
            let uu____14983 =
              let uu____14994 =
                let uu____14995 =
                  let uu____15000 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15000) in
                FStar_SMTEncoding_Util.mkImp uu____14995 in
              ([[typing_pred]], [xx], uu____14994) in
            mkForall_fuel uu____14983 in
          (uu____14982, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14975 in
      [uu____14974] in
    uu____14960 :: uu____14971 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15042 =
      let uu____15043 =
        let uu____15050 =
          let uu____15051 =
            let uu____15062 =
              let uu____15067 =
                let uu____15070 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15070] in
              [uu____15067] in
            let uu____15075 =
              let uu____15076 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15076 tt in
            (uu____15062, [bb], uu____15075) in
          FStar_SMTEncoding_Util.mkForall uu____15051 in
        (uu____15050, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15043 in
    let uu____15097 =
      let uu____15100 =
        let uu____15101 =
          let uu____15108 =
            let uu____15109 =
              let uu____15120 =
                let uu____15121 =
                  let uu____15126 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15126) in
                FStar_SMTEncoding_Util.mkImp uu____15121 in
              ([[typing_pred]], [xx], uu____15120) in
            mkForall_fuel uu____15109 in
          (uu____15108, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15101 in
      [uu____15100] in
    uu____15042 :: uu____15097 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15176 =
        let uu____15177 =
          let uu____15184 =
            let uu____15187 =
              let uu____15190 =
                let uu____15193 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15194 =
                  let uu____15197 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15197] in
                uu____15193 :: uu____15194 in
              tt :: uu____15190 in
            tt :: uu____15187 in
          ("Prims.Precedes", uu____15184) in
        FStar_SMTEncoding_Util.mkApp uu____15177 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15176 in
    let precedes_y_x =
      let uu____15201 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15201 in
    let uu____15204 =
      let uu____15205 =
        let uu____15212 =
          let uu____15213 =
            let uu____15224 =
              let uu____15229 =
                let uu____15232 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15232] in
              [uu____15229] in
            let uu____15237 =
              let uu____15238 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15238 tt in
            (uu____15224, [bb], uu____15237) in
          FStar_SMTEncoding_Util.mkForall uu____15213 in
        (uu____15212, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15205 in
    let uu____15259 =
      let uu____15262 =
        let uu____15263 =
          let uu____15270 =
            let uu____15271 =
              let uu____15282 =
                let uu____15283 =
                  let uu____15288 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15288) in
                FStar_SMTEncoding_Util.mkImp uu____15283 in
              ([[typing_pred]], [xx], uu____15282) in
            mkForall_fuel uu____15271 in
          (uu____15270, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15263 in
      let uu____15313 =
        let uu____15316 =
          let uu____15317 =
            let uu____15324 =
              let uu____15325 =
                let uu____15336 =
                  let uu____15337 =
                    let uu____15342 =
                      let uu____15343 =
                        let uu____15346 =
                          let uu____15349 =
                            let uu____15352 =
                              let uu____15353 =
                                let uu____15358 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15359 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15358, uu____15359) in
                              FStar_SMTEncoding_Util.mkGT uu____15353 in
                            let uu____15360 =
                              let uu____15363 =
                                let uu____15364 =
                                  let uu____15369 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15370 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15369, uu____15370) in
                                FStar_SMTEncoding_Util.mkGTE uu____15364 in
                              let uu____15371 =
                                let uu____15374 =
                                  let uu____15375 =
                                    let uu____15380 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15381 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15380, uu____15381) in
                                  FStar_SMTEncoding_Util.mkLT uu____15375 in
                                [uu____15374] in
                              uu____15363 :: uu____15371 in
                            uu____15352 :: uu____15360 in
                          typing_pred_y :: uu____15349 in
                        typing_pred :: uu____15346 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15343 in
                    (uu____15342, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15337 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15336) in
              mkForall_fuel uu____15325 in
            (uu____15324,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15317 in
        [uu____15316] in
      uu____15262 :: uu____15313 in
    uu____15204 :: uu____15259 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15427 =
      let uu____15428 =
        let uu____15435 =
          let uu____15436 =
            let uu____15447 =
              let uu____15452 =
                let uu____15455 = FStar_SMTEncoding_Term.boxString b in
                [uu____15455] in
              [uu____15452] in
            let uu____15460 =
              let uu____15461 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15461 tt in
            (uu____15447, [bb], uu____15460) in
          FStar_SMTEncoding_Util.mkForall uu____15436 in
        (uu____15435, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15428 in
    let uu____15482 =
      let uu____15485 =
        let uu____15486 =
          let uu____15493 =
            let uu____15494 =
              let uu____15505 =
                let uu____15506 =
                  let uu____15511 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15511) in
                FStar_SMTEncoding_Util.mkImp uu____15506 in
              ([[typing_pred]], [xx], uu____15505) in
            mkForall_fuel uu____15494 in
          (uu____15493, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15486 in
      [uu____15485] in
    uu____15427 :: uu____15482 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15564 =
      let uu____15565 =
        let uu____15572 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15572, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15565 in
    [uu____15564] in
  let mk_and_interp env conj uu____15584 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15609 =
      let uu____15610 =
        let uu____15617 =
          let uu____15618 =
            let uu____15629 =
              let uu____15630 =
                let uu____15635 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15635, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15630 in
            ([[l_and_a_b]], [aa; bb], uu____15629) in
          FStar_SMTEncoding_Util.mkForall uu____15618 in
        (uu____15617, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15610 in
    [uu____15609] in
  let mk_or_interp env disj uu____15673 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15698 =
      let uu____15699 =
        let uu____15706 =
          let uu____15707 =
            let uu____15718 =
              let uu____15719 =
                let uu____15724 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15724, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15719 in
            ([[l_or_a_b]], [aa; bb], uu____15718) in
          FStar_SMTEncoding_Util.mkForall uu____15707 in
        (uu____15706, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15699 in
    [uu____15698] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15787 =
      let uu____15788 =
        let uu____15795 =
          let uu____15796 =
            let uu____15807 =
              let uu____15808 =
                let uu____15813 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15813, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15808 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15807) in
          FStar_SMTEncoding_Util.mkForall uu____15796 in
        (uu____15795, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15788 in
    [uu____15787] in
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
    let uu____15886 =
      let uu____15887 =
        let uu____15894 =
          let uu____15895 =
            let uu____15906 =
              let uu____15907 =
                let uu____15912 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15912, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15907 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15906) in
          FStar_SMTEncoding_Util.mkForall uu____15895 in
        (uu____15894, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15887 in
    [uu____15886] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15983 =
      let uu____15984 =
        let uu____15991 =
          let uu____15992 =
            let uu____16003 =
              let uu____16004 =
                let uu____16009 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16009, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16004 in
            ([[l_imp_a_b]], [aa; bb], uu____16003) in
          FStar_SMTEncoding_Util.mkForall uu____15992 in
        (uu____15991, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15984 in
    [uu____15983] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16072 =
      let uu____16073 =
        let uu____16080 =
          let uu____16081 =
            let uu____16092 =
              let uu____16093 =
                let uu____16098 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16098, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16093 in
            ([[l_iff_a_b]], [aa; bb], uu____16092) in
          FStar_SMTEncoding_Util.mkForall uu____16081 in
        (uu____16080, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16073 in
    [uu____16072] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16150 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16150 in
    let uu____16153 =
      let uu____16154 =
        let uu____16161 =
          let uu____16162 =
            let uu____16173 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16173) in
          FStar_SMTEncoding_Util.mkForall uu____16162 in
        (uu____16161, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16154 in
    [uu____16153] in
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
      let uu____16233 =
        let uu____16240 =
          let uu____16243 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16243] in
        ("Valid", uu____16240) in
      FStar_SMTEncoding_Util.mkApp uu____16233 in
    let uu____16246 =
      let uu____16247 =
        let uu____16254 =
          let uu____16255 =
            let uu____16266 =
              let uu____16267 =
                let uu____16272 =
                  let uu____16273 =
                    let uu____16284 =
                      let uu____16289 =
                        let uu____16292 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16292] in
                      [uu____16289] in
                    let uu____16297 =
                      let uu____16298 =
                        let uu____16303 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16303, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16298 in
                    (uu____16284, [xx1], uu____16297) in
                  FStar_SMTEncoding_Util.mkForall uu____16273 in
                (uu____16272, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16267 in
            ([[l_forall_a_b]], [aa; bb], uu____16266) in
          FStar_SMTEncoding_Util.mkForall uu____16255 in
        (uu____16254, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16247 in
    [uu____16246] in
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
      let uu____16385 =
        let uu____16392 =
          let uu____16395 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16395] in
        ("Valid", uu____16392) in
      FStar_SMTEncoding_Util.mkApp uu____16385 in
    let uu____16398 =
      let uu____16399 =
        let uu____16406 =
          let uu____16407 =
            let uu____16418 =
              let uu____16419 =
                let uu____16424 =
                  let uu____16425 =
                    let uu____16436 =
                      let uu____16441 =
                        let uu____16444 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16444] in
                      [uu____16441] in
                    let uu____16449 =
                      let uu____16450 =
                        let uu____16455 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16455, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16450 in
                    (uu____16436, [xx1], uu____16449) in
                  FStar_SMTEncoding_Util.mkExists uu____16425 in
                (uu____16424, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16419 in
            ([[l_exists_a_b]], [aa; bb], uu____16418) in
          FStar_SMTEncoding_Util.mkForall uu____16407 in
        (uu____16406, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16399 in
    [uu____16398] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16515 =
      let uu____16516 =
        let uu____16523 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16524 = varops.mk_unique "typing_range_const" in
        (uu____16523, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16524) in
      FStar_SMTEncoding_Util.mkAssume uu____16516 in
    [uu____16515] in
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
        let uu____16558 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16558 x1 t in
      let uu____16559 =
        let uu____16570 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16570) in
      FStar_SMTEncoding_Util.mkForall uu____16559 in
    let uu____16593 =
      let uu____16594 =
        let uu____16601 =
          let uu____16602 =
            let uu____16613 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16613) in
          FStar_SMTEncoding_Util.mkForall uu____16602 in
        (uu____16601,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16594 in
    [uu____16593] in
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
          let uu____16937 =
            FStar_Util.find_opt
              (fun uu____16963  ->
                 match uu____16963 with
                 | (l,uu____16975) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16937 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17000,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17039 = encode_function_type_as_formula t env in
        match uu____17039 with
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
              let uu____17085 =
                ((let uu____17088 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17088) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17085
              then
                let uu____17095 = new_term_constant_and_tok_from_lid env lid in
                match uu____17095 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17114 =
                        let uu____17115 = FStar_Syntax_Subst.compress t_norm in
                        uu____17115.FStar_Syntax_Syntax.n in
                      match uu____17114 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17121) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17151  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17156 -> [] in
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
                (let uu____17170 = prims.is lid in
                 if uu____17170
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17178 = prims.mk lid vname in
                   match uu____17178 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17202 =
                      let uu____17213 = curried_arrow_formals_comp t_norm in
                      match uu____17213 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17231 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17231
                            then
                              let uu____17232 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___149_17235 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___149_17235.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___149_17235.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___149_17235.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___149_17235.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___149_17235.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___149_17235.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___149_17235.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___149_17235.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___149_17235.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___149_17235.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___149_17235.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___149_17235.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___149_17235.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___149_17235.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___149_17235.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___149_17235.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___149_17235.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___149_17235.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___149_17235.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___149_17235.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___149_17235.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___149_17235.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___149_17235.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___149_17235.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___149_17235.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___149_17235.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___149_17235.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___149_17235.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___149_17235.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17232
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17247 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17247)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17202 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17292 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17292 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17313 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___121_17355  ->
                                       match uu___121_17355 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17359 =
                                             FStar_Util.prefix vars in
                                           (match uu____17359 with
                                            | (uu____17380,(xxsym,uu____17382))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17400 =
                                                  let uu____17401 =
                                                    let uu____17408 =
                                                      let uu____17409 =
                                                        let uu____17420 =
                                                          let uu____17421 =
                                                            let uu____17426 =
                                                              let uu____17427
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17427 in
                                                            (vapp,
                                                              uu____17426) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17421 in
                                                        ([[vapp]], vars,
                                                          uu____17420) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17409 in
                                                    (uu____17408,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17401 in
                                                [uu____17400])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17446 =
                                             FStar_Util.prefix vars in
                                           (match uu____17446 with
                                            | (uu____17467,(xxsym,uu____17469))
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
                                                let uu____17492 =
                                                  let uu____17493 =
                                                    let uu____17500 =
                                                      let uu____17501 =
                                                        let uu____17512 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17512) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17501 in
                                                    (uu____17500,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17493 in
                                                [uu____17492])
                                       | uu____17529 -> [])) in
                             let uu____17530 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17530 with
                              | (vars,guards,env',decls1,uu____17557) ->
                                  let uu____17570 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17579 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17579, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17581 =
                                          encode_formula p env' in
                                        (match uu____17581 with
                                         | (g,ds) ->
                                             let uu____17592 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17592,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17570 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17605 =
                                           let uu____17612 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17612) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17605 in
                                       let uu____17621 =
                                         let vname_decl =
                                           let uu____17629 =
                                             let uu____17640 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17650  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17640,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17629 in
                                         let uu____17659 =
                                           let env2 =
                                             let uu___150_17665 = env1 in
                                             {
                                               bindings =
                                                 (uu___150_17665.bindings);
                                               depth = (uu___150_17665.depth);
                                               tcenv = (uu___150_17665.tcenv);
                                               warn = (uu___150_17665.warn);
                                               cache = (uu___150_17665.cache);
                                               nolabels =
                                                 (uu___150_17665.nolabels);
                                               use_zfuel_name =
                                                 (uu___150_17665.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___150_17665.current_module_name)
                                             } in
                                           let uu____17666 =
                                             let uu____17667 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17667 in
                                           if uu____17666
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17659 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17682::uu____17683 ->
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
                                                     let uu____17723 =
                                                       let uu____17734 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17734) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17723 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17761 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17764 =
                                               match formals with
                                               | [] ->
                                                   let uu____17781 =
                                                     let uu____17782 =
                                                       let uu____17785 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17785 in
                                                     push_free_var env1 lid
                                                       vname uu____17782 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17781)
                                               | uu____17790 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17797 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17797 in
                                                   let name_tok_corr =
                                                     let uu____17799 =
                                                       let uu____17806 =
                                                         let uu____17807 =
                                                           let uu____17818 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17818) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17807 in
                                                       (uu____17806,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17799 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17764 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17621 with
                                        | (decls2,env2) ->
                                            let uu____17861 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17869 =
                                                encode_term res_t1 env' in
                                              match uu____17869 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17882 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17882, decls) in
                                            (match uu____17861 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17893 =
                                                     let uu____17900 =
                                                       let uu____17901 =
                                                         let uu____17912 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17912) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17901 in
                                                     (uu____17900,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17893 in
                                                 let freshness =
                                                   let uu____17928 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17928
                                                   then
                                                     let uu____17933 =
                                                       let uu____17934 =
                                                         let uu____17945 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17956 =
                                                           varops.next_id () in
                                                         (vname, uu____17945,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17956) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17934 in
                                                     let uu____17959 =
                                                       let uu____17962 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17962] in
                                                     uu____17933 ::
                                                       uu____17959
                                                   else [] in
                                                 let g =
                                                   let uu____17967 =
                                                     let uu____17970 =
                                                       let uu____17973 =
                                                         let uu____17976 =
                                                           let uu____17979 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17979 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17976 in
                                                       FStar_List.append
                                                         decls3 uu____17973 in
                                                     FStar_List.append decls2
                                                       uu____17970 in
                                                   FStar_List.append decls11
                                                     uu____17967 in
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
          let uu____18014 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18014 with
          | FStar_Pervasives_Native.None  ->
              let uu____18051 = encode_free_var false env x t t_norm [] in
              (match uu____18051 with
               | (decls,env1) ->
                   let uu____18078 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18078 with
                    | (n1,x',uu____18105) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18126) ->
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
            let uu____18186 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18186 with
            | (decls,env1) ->
                let uu____18205 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18205
                then
                  let uu____18212 =
                    let uu____18215 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18215 in
                  (uu____18212, env1)
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
             (fun uu____18270  ->
                fun lb  ->
                  match uu____18270 with
                  | (decls,env1) ->
                      let uu____18290 =
                        let uu____18297 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18297
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18290 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18319 = FStar_Syntax_Util.head_and_args t in
    match uu____18319 with
    | (hd1,args) ->
        let uu____18356 =
          let uu____18357 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18357.FStar_Syntax_Syntax.n in
        (match uu____18356 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18361,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18380 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18405  ->
      fun quals  ->
        match uu____18405 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18481 = FStar_Util.first_N nbinders formals in
              match uu____18481 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18562  ->
                         fun uu____18563  ->
                           match (uu____18562, uu____18563) with
                           | ((formal,uu____18581),(binder,uu____18583)) ->
                               let uu____18592 =
                                 let uu____18599 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18599) in
                               FStar_Syntax_Syntax.NT uu____18592) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18607 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18638  ->
                              match uu____18638 with
                              | (x,i) ->
                                  let uu____18649 =
                                    let uu___151_18650 = x in
                                    let uu____18651 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___151_18650.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___151_18650.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18651
                                    } in
                                  (uu____18649, i))) in
                    FStar_All.pipe_right uu____18607
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18669 =
                      let uu____18670 = FStar_Syntax_Subst.compress body in
                      let uu____18671 =
                        let uu____18672 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18672 in
                      FStar_Syntax_Syntax.extend_app_n uu____18670
                        uu____18671 in
                    uu____18669 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18733 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18733
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___152_18736 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_18736.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_18736.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_18736.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_18736.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_18736.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_18736.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_18736.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_18736.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_18736.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_18736.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_18736.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_18736.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_18736.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_18736.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_18736.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_18736.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_18736.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_18736.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_18736.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___152_18736.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___152_18736.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_18736.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_18736.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_18736.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_18736.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___152_18736.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___152_18736.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___152_18736.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___152_18736.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18769 = FStar_Syntax_Util.abs_formals e in
                match uu____18769 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18833::uu____18834 ->
                         let uu____18849 =
                           let uu____18850 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18850.FStar_Syntax_Syntax.n in
                         (match uu____18849 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18895 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18895 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18937 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18937
                                   then
                                     let uu____18972 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18972 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19066  ->
                                                   fun uu____19067  ->
                                                     match (uu____19066,
                                                             uu____19067)
                                                     with
                                                     | ((x,uu____19085),
                                                        (b,uu____19087)) ->
                                                         let uu____19096 =
                                                           let uu____19103 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19103) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19096)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19105 =
                                            let uu____19126 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19126) in
                                          (uu____19105, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19194 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19194 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19283) ->
                              let uu____19288 =
                                let uu____19309 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19309 in
                              (uu____19288, true)
                          | uu____19374 when Prims.op_Negation norm1 ->
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
                          | uu____19376 ->
                              let uu____19377 =
                                let uu____19378 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19379 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19378
                                  uu____19379 in
                              failwith uu____19377)
                     | uu____19404 ->
                         let uu____19405 =
                           let uu____19406 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19406.FStar_Syntax_Syntax.n in
                         (match uu____19405 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19451 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19451 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19483 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19483 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19566 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19622 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19622
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19634 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19728  ->
                            fun lb  ->
                              match uu____19728 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19823 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19823
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19826 =
                                      let uu____19841 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19841
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19826 with
                                    | (tok,decl,env2) ->
                                        let uu____19887 =
                                          let uu____19900 =
                                            let uu____19911 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19911, tok) in
                                          uu____19900 :: toks in
                                        (uu____19887, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19634 with
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
                        | uu____20094 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20102 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20102 vars)
                            else
                              (let uu____20104 =
                                 let uu____20111 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20111) in
                               FStar_SMTEncoding_Util.mkApp uu____20104) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20193;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20195;
                             FStar_Syntax_Syntax.lbeff = uu____20196;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20259 =
                              let uu____20266 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20266 with
                              | (tcenv',uu____20284,e_t) ->
                                  let uu____20290 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20301 -> failwith "Impossible" in
                                  (match uu____20290 with
                                   | (e1,t_norm1) ->
                                       ((let uu___155_20317 = env2 in
                                         {
                                           bindings =
                                             (uu___155_20317.bindings);
                                           depth = (uu___155_20317.depth);
                                           tcenv = tcenv';
                                           warn = (uu___155_20317.warn);
                                           cache = (uu___155_20317.cache);
                                           nolabels =
                                             (uu___155_20317.nolabels);
                                           use_zfuel_name =
                                             (uu___155_20317.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___155_20317.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___155_20317.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20259 with
                             | (env',e1,t_norm1) ->
                                 let uu____20327 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20327 with
                                  | ((binders,body,uu____20348,uu____20349),curry)
                                      ->
                                      ((let uu____20360 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20360
                                        then
                                          let uu____20361 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20362 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20361 uu____20362
                                        else ());
                                       (let uu____20364 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20364 with
                                        | (vars,guards,env'1,binder_decls,uu____20391)
                                            ->
                                            let body1 =
                                              let uu____20405 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20405
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20408 =
                                              let uu____20417 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20417
                                              then
                                                let uu____20428 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20429 =
                                                  encode_formula body1 env'1 in
                                                (uu____20428, uu____20429)
                                              else
                                                (let uu____20439 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20439)) in
                                            (match uu____20408 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20462 =
                                                     let uu____20469 =
                                                       let uu____20470 =
                                                         let uu____20481 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20481) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20470 in
                                                     let uu____20492 =
                                                       let uu____20495 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20495 in
                                                     (uu____20469,
                                                       uu____20492,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20462 in
                                                 let uu____20498 =
                                                   let uu____20501 =
                                                     let uu____20504 =
                                                       let uu____20507 =
                                                         let uu____20510 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20510 in
                                                       FStar_List.append
                                                         decls2 uu____20507 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20504 in
                                                   FStar_List.append decls1
                                                     uu____20501 in
                                                 (uu____20498, env2))))))
                        | uu____20515 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20600 = varops.fresh "fuel" in
                          (uu____20600, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20603 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20691  ->
                                  fun uu____20692  ->
                                    match (uu____20691, uu____20692) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20840 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20840 in
                                        let gtok =
                                          let uu____20842 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20842 in
                                        let env4 =
                                          let uu____20844 =
                                            let uu____20847 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20847 in
                                          push_free_var env3 flid gtok
                                            uu____20844 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20603 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____21003 t_norm
                              uu____21005 =
                              match (uu____21003, uu____21005) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21049;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21050;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21078 =
                                    let uu____21085 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____21085 with
                                    | (tcenv',uu____21107,e_t) ->
                                        let uu____21113 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21124 ->
                                              failwith "Impossible" in
                                        (match uu____21113 with
                                         | (e1,t_norm1) ->
                                             ((let uu___156_21140 = env3 in
                                               {
                                                 bindings =
                                                   (uu___156_21140.bindings);
                                                 depth =
                                                   (uu___156_21140.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___156_21140.warn);
                                                 cache =
                                                   (uu___156_21140.cache);
                                                 nolabels =
                                                   (uu___156_21140.nolabels);
                                                 use_zfuel_name =
                                                   (uu___156_21140.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___156_21140.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___156_21140.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____21078 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21155 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21155
                                         then
                                           let uu____21156 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21157 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21158 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21156 uu____21157
                                             uu____21158
                                         else ());
                                        (let uu____21160 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21160 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21197 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21197
                                               then
                                                 let uu____21198 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21199 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21200 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21201 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21198 uu____21199
                                                   uu____21200 uu____21201
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21205 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21205 with
                                               | (vars,guards,env'1,binder_decls,uu____21236)
                                                   ->
                                                   let decl_g =
                                                     let uu____21250 =
                                                       let uu____21261 =
                                                         let uu____21264 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21264 in
                                                       (g, uu____21261,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21250 in
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
                                                     let uu____21289 =
                                                       let uu____21296 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21296) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21289 in
                                                   let gsapp =
                                                     let uu____21306 =
                                                       let uu____21313 =
                                                         let uu____21316 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21316 ::
                                                           vars_tm in
                                                       (g, uu____21313) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21306 in
                                                   let gmax =
                                                     let uu____21322 =
                                                       let uu____21329 =
                                                         let uu____21332 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21332 ::
                                                           vars_tm in
                                                       (g, uu____21329) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21322 in
                                                   let body1 =
                                                     let uu____21338 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21338
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21340 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21340 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21358 =
                                                            let uu____21365 =
                                                              let uu____21366
                                                                =
                                                                let uu____21381
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
                                                                  uu____21381) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21366 in
                                                            let uu____21402 =
                                                              let uu____21405
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21405 in
                                                            (uu____21365,
                                                              uu____21402,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21358 in
                                                        let eqn_f =
                                                          let uu____21409 =
                                                            let uu____21416 =
                                                              let uu____21417
                                                                =
                                                                let uu____21428
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21428) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21417 in
                                                            (uu____21416,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21409 in
                                                        let eqn_g' =
                                                          let uu____21442 =
                                                            let uu____21449 =
                                                              let uu____21450
                                                                =
                                                                let uu____21461
                                                                  =
                                                                  let uu____21462
                                                                    =
                                                                    let uu____21467
                                                                    =
                                                                    let uu____21468
                                                                    =
                                                                    let uu____21475
                                                                    =
                                                                    let uu____21478
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21478
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21475) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21468 in
                                                                    (gsapp,
                                                                    uu____21467) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21462 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21461) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21450 in
                                                            (uu____21449,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21442 in
                                                        let uu____21501 =
                                                          let uu____21510 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21510
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21539)
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
                                                                  let uu____21564
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21564
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21569
                                                                  =
                                                                  let uu____21576
                                                                    =
                                                                    let uu____21577
                                                                    =
                                                                    let uu____21588
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21588) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21577 in
                                                                  (uu____21576,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21569 in
                                                              let uu____21609
                                                                =
                                                                let uu____21616
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21616
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21629
                                                                    =
                                                                    let uu____21632
                                                                    =
                                                                    let uu____21633
                                                                    =
                                                                    let uu____21640
                                                                    =
                                                                    let uu____21641
                                                                    =
                                                                    let uu____21652
                                                                    =
                                                                    let uu____21653
                                                                    =
                                                                    let uu____21658
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21658,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21653 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21652) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21641 in
                                                                    (uu____21640,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21633 in
                                                                    [uu____21632] in
                                                                    (d3,
                                                                    uu____21629) in
                                                              (match uu____21609
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21501
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
                            let uu____21723 =
                              let uu____21736 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21815  ->
                                   fun uu____21816  ->
                                     match (uu____21815, uu____21816) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21971 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21971 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21736 in
                            (match uu____21723 with
                             | (decls2,eqns,env01) ->
                                 let uu____22044 =
                                   let isDeclFun uu___122_22056 =
                                     match uu___122_22056 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22057 -> true
                                     | uu____22068 -> false in
                                   let uu____22069 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____22069
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____22044 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____22109 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___123_22113  ->
                                 match uu___123_22113 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22114 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22120 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22120))) in
                      if uu____22109
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
                   let uu____22172 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22172
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
        let uu____22221 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22221 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22225 = encode_sigelt' env se in
      match uu____22225 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22241 =
                  let uu____22242 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22242 in
                [uu____22241]
            | uu____22243 ->
                let uu____22244 =
                  let uu____22247 =
                    let uu____22248 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22248 in
                  uu____22247 :: g in
                let uu____22249 =
                  let uu____22252 =
                    let uu____22253 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22253 in
                  [uu____22252] in
                FStar_List.append uu____22244 uu____22249 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22266 =
          let uu____22267 = FStar_Syntax_Subst.compress t in
          uu____22267.FStar_Syntax_Syntax.n in
        match uu____22266 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22271)) -> s = "opaque_to_smt"
        | uu____22272 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22277 =
          let uu____22278 = FStar_Syntax_Subst.compress t in
          uu____22278.FStar_Syntax_Syntax.n in
        match uu____22277 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22282)) -> s = "uninterpreted_by_smt"
        | uu____22283 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22288 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22293 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22296 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22299 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22314 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22318 =
            let uu____22319 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22319 Prims.op_Negation in
          if uu____22318
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22345 ->
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
               let uu____22365 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22365 with
               | (aname,atok,env2) ->
                   let uu____22381 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22381 with
                    | (formals,uu____22399) ->
                        let uu____22412 =
                          let uu____22417 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22417 env2 in
                        (match uu____22412 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22429 =
                                 let uu____22430 =
                                   let uu____22441 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22457  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22441,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22430 in
                               [uu____22429;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22470 =
                               let aux uu____22522 uu____22523 =
                                 match (uu____22522, uu____22523) with
                                 | ((bv,uu____22575),(env3,acc_sorts,acc)) ->
                                     let uu____22613 = gen_term_var env3 bv in
                                     (match uu____22613 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22470 with
                              | (uu____22685,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22708 =
                                      let uu____22715 =
                                        let uu____22716 =
                                          let uu____22727 =
                                            let uu____22728 =
                                              let uu____22733 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22733) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22728 in
                                          ([[app]], xs_sorts, uu____22727) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22716 in
                                      (uu____22715,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22708 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22753 =
                                      let uu____22760 =
                                        let uu____22761 =
                                          let uu____22772 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22772) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22761 in
                                      (uu____22760,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22753 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22791 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22791 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22819,uu____22820)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22821 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22821 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22838,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22844 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___124_22848  ->
                      match uu___124_22848 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22849 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22854 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22855 -> false)) in
            Prims.op_Negation uu____22844 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22864 =
               let uu____22871 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22871 env fv t quals in
             match uu____22864 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22886 =
                   let uu____22889 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22889 in
                 (uu____22886, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22897 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22897 with
           | (uu____22906,f1) ->
               let uu____22908 = encode_formula f1 env in
               (match uu____22908 with
                | (f2,decls) ->
                    let g =
                      let uu____22922 =
                        let uu____22923 =
                          let uu____22930 =
                            let uu____22933 =
                              let uu____22934 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22934 in
                            FStar_Pervasives_Native.Some uu____22933 in
                          let uu____22935 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22930, uu____22935) in
                        FStar_SMTEncoding_Util.mkAssume uu____22923 in
                      [uu____22922] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22941) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22953 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22971 =
                       let uu____22974 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22974.FStar_Syntax_Syntax.fv_name in
                     uu____22971.FStar_Syntax_Syntax.v in
                   let uu____22975 =
                     let uu____22976 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22976 in
                   if uu____22975
                   then
                     let val_decl =
                       let uu___159_23004 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___159_23004.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___159_23004.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___159_23004.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23009 = encode_sigelt' env1 val_decl in
                     match uu____23009 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22953 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23037,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23039;
                          FStar_Syntax_Syntax.lbtyp = uu____23040;
                          FStar_Syntax_Syntax.lbeff = uu____23041;
                          FStar_Syntax_Syntax.lbdef = uu____23042;_}::[]),uu____23043)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23062 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23062 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23091 =
                   let uu____23094 =
                     let uu____23095 =
                       let uu____23102 =
                         let uu____23103 =
                           let uu____23114 =
                             let uu____23115 =
                               let uu____23120 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23120) in
                             FStar_SMTEncoding_Util.mkEq uu____23115 in
                           ([[b2t_x]], [xx], uu____23114) in
                         FStar_SMTEncoding_Util.mkForall uu____23103 in
                       (uu____23102,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23095 in
                   [uu____23094] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23091 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23153,uu____23154) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_23163  ->
                  match uu___125_23163 with
                  | FStar_Syntax_Syntax.Discriminator uu____23164 -> true
                  | uu____23165 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23168,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23179 =
                     let uu____23180 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23180.FStar_Ident.idText in
                   uu____23179 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___126_23184  ->
                     match uu___126_23184 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23185 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23189) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___127_23206  ->
                  match uu___127_23206 with
                  | FStar_Syntax_Syntax.Projector uu____23207 -> true
                  | uu____23212 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23215 = try_lookup_free_var env l in
          (match uu____23215 with
           | FStar_Pervasives_Native.Some uu____23222 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___160_23226 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___160_23226.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___160_23226.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___160_23226.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23233) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23251) ->
          let uu____23260 = encode_sigelts env ses in
          (match uu____23260 with
           | (g,env1) ->
               let uu____23277 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___128_23300  ->
                         match uu___128_23300 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23301;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23302;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23303;_}
                             -> false
                         | uu____23306 -> true)) in
               (match uu____23277 with
                | (g',inversions) ->
                    let uu____23321 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___129_23342  ->
                              match uu___129_23342 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23343 ->
                                  true
                              | uu____23354 -> false)) in
                    (match uu____23321 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23372,tps,k,uu____23375,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___130_23392  ->
                    match uu___130_23392 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23393 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23402 = c in
              match uu____23402 with
              | (name,args,uu____23407,uu____23408,uu____23409) ->
                  let uu____23414 =
                    let uu____23415 =
                      let uu____23426 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23443  ->
                                match uu____23443 with
                                | (uu____23450,sort,uu____23452) -> sort)) in
                      (name, uu____23426, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23415 in
                  [uu____23414]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23479 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23485 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23485 FStar_Option.isNone)) in
            if uu____23479
            then []
            else
              (let uu____23517 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23517 with
               | (xxsym,xx) ->
                   let uu____23526 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23565  ->
                             fun l  ->
                               match uu____23565 with
                               | (out,decls) ->
                                   let uu____23585 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23585 with
                                    | (uu____23596,data_t) ->
                                        let uu____23598 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23598 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23644 =
                                                 let uu____23645 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23645.FStar_Syntax_Syntax.n in
                                               match uu____23644 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23656,indices) ->
                                                   indices
                                               | uu____23678 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23702  ->
                                                         match uu____23702
                                                         with
                                                         | (x,uu____23708) ->
                                                             let uu____23709
                                                               =
                                                               let uu____23710
                                                                 =
                                                                 let uu____23717
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23717,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23710 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23709)
                                                    env) in
                                             let uu____23720 =
                                               encode_args indices env1 in
                                             (match uu____23720 with
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
                                                      let uu____23746 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23762
                                                                 =
                                                                 let uu____23767
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23767,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23762)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23746
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23770 =
                                                      let uu____23771 =
                                                        let uu____23776 =
                                                          let uu____23777 =
                                                            let uu____23782 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23782,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23777 in
                                                        (out, uu____23776) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23771 in
                                                    (uu____23770,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23526 with
                    | (data_ax,decls) ->
                        let uu____23795 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23795 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23806 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23806 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23810 =
                                 let uu____23817 =
                                   let uu____23818 =
                                     let uu____23829 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23844 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23829,
                                       uu____23844) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23818 in
                                 let uu____23859 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23817,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23859) in
                               FStar_SMTEncoding_Util.mkAssume uu____23810 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23862 =
            let uu____23875 =
              let uu____23876 = FStar_Syntax_Subst.compress k in
              uu____23876.FStar_Syntax_Syntax.n in
            match uu____23875 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23921 -> (tps, k) in
          (match uu____23862 with
           | (formals,res) ->
               let uu____23944 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23944 with
                | (formals1,res1) ->
                    let uu____23955 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23955 with
                     | (vars,guards,env',binder_decls,uu____23980) ->
                         let uu____23993 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23993 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24012 =
                                  let uu____24019 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24019) in
                                FStar_SMTEncoding_Util.mkApp uu____24012 in
                              let uu____24028 =
                                let tname_decl =
                                  let uu____24038 =
                                    let uu____24039 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24071  ->
                                              match uu____24071 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24084 = varops.next_id () in
                                    (tname, uu____24039,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24084, false) in
                                  constructor_or_logic_type_decl uu____24038 in
                                let uu____24093 =
                                  match vars with
                                  | [] ->
                                      let uu____24106 =
                                        let uu____24107 =
                                          let uu____24110 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____24110 in
                                        push_free_var env1 t tname
                                          uu____24107 in
                                      ([], uu____24106)
                                  | uu____24117 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24126 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24126 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24140 =
                                          let uu____24147 =
                                            let uu____24148 =
                                              let uu____24163 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24163) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24148 in
                                          (uu____24147,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24140 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24093 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24028 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24203 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24203 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24221 =
                                               let uu____24222 =
                                                 let uu____24229 =
                                                   let uu____24230 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24230 in
                                                 (uu____24229,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24222 in
                                             [uu____24221]
                                           else [] in
                                         let uu____24234 =
                                           let uu____24237 =
                                             let uu____24240 =
                                               let uu____24241 =
                                                 let uu____24248 =
                                                   let uu____24249 =
                                                     let uu____24260 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24260) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24249 in
                                                 (uu____24248,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24241 in
                                             [uu____24240] in
                                           FStar_List.append karr uu____24237 in
                                         FStar_List.append decls1 uu____24234 in
                                   let aux =
                                     let uu____24276 =
                                       let uu____24279 =
                                         inversion_axioms tapp vars in
                                       let uu____24282 =
                                         let uu____24285 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24285] in
                                       FStar_List.append uu____24279
                                         uu____24282 in
                                     FStar_List.append kindingAx uu____24276 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24292,uu____24293,uu____24294,uu____24295,uu____24296)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24304,t,uu____24306,n_tps,uu____24308) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24316 = new_term_constant_and_tok_from_lid env d in
          (match uu____24316 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24333 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24333 with
                | (formals,t_res) ->
                    let uu____24368 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24368 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24382 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24382 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24452 =
                                            mk_term_projector_name d x in
                                          (uu____24452,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24454 =
                                  let uu____24473 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24473, true) in
                                FStar_All.pipe_right uu____24454
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
                              let uu____24512 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24512 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24524::uu____24525 ->
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
                                         let uu____24570 =
                                           let uu____24581 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24581) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24570
                                     | uu____24606 -> tok_typing in
                                   let uu____24615 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24615 with
                                    | (vars',guards',env'',decls_formals,uu____24640)
                                        ->
                                        let uu____24653 =
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
                                        (match uu____24653 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24684 ->
                                                   let uu____24691 =
                                                     let uu____24692 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24692 in
                                                   [uu____24691] in
                                             let encode_elim uu____24702 =
                                               let uu____24703 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24703 with
                                               | (head1,args) ->
                                                   let uu____24746 =
                                                     let uu____24747 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24747.FStar_Syntax_Syntax.n in
                                                   (match uu____24746 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24757;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24758;_},uu____24759)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24765 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24765
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
                                                                 | uu____24808
                                                                    ->
                                                                    let uu____24809
                                                                    =
                                                                    let uu____24810
                                                                    =
                                                                    let uu____24815
                                                                    =
                                                                    let uu____24816
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24816 in
                                                                    (uu____24815,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24810 in
                                                                    FStar_Exn.raise
                                                                    uu____24809 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24832
                                                                    =
                                                                    let uu____24833
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24833 in
                                                                    if
                                                                    uu____24832
                                                                    then
                                                                    let uu____24846
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24846]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24848
                                                               =
                                                               let uu____24861
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24911
                                                                     ->
                                                                    fun
                                                                    uu____24912
                                                                     ->
                                                                    match 
                                                                    (uu____24911,
                                                                    uu____24912)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25007
                                                                    =
                                                                    let uu____25014
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25014 in
                                                                    (match uu____25007
                                                                    with
                                                                    | 
                                                                    (uu____25027,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25035
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25035
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25037
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25037
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
                                                                 uu____24861 in
                                                             (match uu____24848
                                                              with
                                                              | (uu____25052,arg_vars,elim_eqns_or_guards,uu____25055)
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
                                                                    let uu____25085
                                                                    =
                                                                    let uu____25092
                                                                    =
                                                                    let uu____25093
                                                                    =
                                                                    let uu____25104
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25115
                                                                    =
                                                                    let uu____25116
                                                                    =
                                                                    let uu____25121
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25121) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25116 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25104,
                                                                    uu____25115) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25093 in
                                                                    (uu____25092,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25085 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25144
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25144,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25146
                                                                    =
                                                                    let uu____25153
                                                                    =
                                                                    let uu____25154
                                                                    =
                                                                    let uu____25165
                                                                    =
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25173
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25173] in
                                                                    [uu____25170] in
                                                                    let uu____25178
                                                                    =
                                                                    let uu____25179
                                                                    =
                                                                    let uu____25184
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25185
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25184,
                                                                    uu____25185) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25179 in
                                                                    (uu____25165,
                                                                    [x],
                                                                    uu____25178) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25154 in
                                                                    let uu____25204
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25153,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25204) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25146
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25211
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
                                                                    (let uu____25239
                                                                    =
                                                                    let uu____25240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25240
                                                                    dapp1 in
                                                                    [uu____25239]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25211
                                                                    FStar_List.flatten in
                                                                    let uu____25247
                                                                    =
                                                                    let uu____25254
                                                                    =
                                                                    let uu____25255
                                                                    =
                                                                    let uu____25266
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25277
                                                                    =
                                                                    let uu____25278
                                                                    =
                                                                    let uu____25283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25283) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25278 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25266,
                                                                    uu____25277) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25255 in
                                                                    (uu____25254,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25247) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25304 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25304
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
                                                                 | uu____25347
                                                                    ->
                                                                    let uu____25348
                                                                    =
                                                                    let uu____25349
                                                                    =
                                                                    let uu____25354
                                                                    =
                                                                    let uu____25355
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25355 in
                                                                    (uu____25354,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25349 in
                                                                    FStar_Exn.raise
                                                                    uu____25348 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25371
                                                                    =
                                                                    let uu____25372
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25372 in
                                                                    if
                                                                    uu____25371
                                                                    then
                                                                    let uu____25385
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25385]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25387
                                                               =
                                                               let uu____25400
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25450
                                                                     ->
                                                                    fun
                                                                    uu____25451
                                                                     ->
                                                                    match 
                                                                    (uu____25450,
                                                                    uu____25451)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25546
                                                                    =
                                                                    let uu____25553
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25553 in
                                                                    (match uu____25546
                                                                    with
                                                                    | 
                                                                    (uu____25566,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25574
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25574
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25576
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25576
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
                                                                 uu____25400 in
                                                             (match uu____25387
                                                              with
                                                              | (uu____25591,arg_vars,elim_eqns_or_guards,uu____25594)
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
                                                                    let uu____25624
                                                                    =
                                                                    let uu____25631
                                                                    =
                                                                    let uu____25632
                                                                    =
                                                                    let uu____25643
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25655
                                                                    =
                                                                    let uu____25660
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25660) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25655 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25643,
                                                                    uu____25654) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25632 in
                                                                    (uu____25631,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25624 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25683
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25683,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25685
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    let uu____25693
                                                                    =
                                                                    let uu____25704
                                                                    =
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25712
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25712] in
                                                                    [uu____25709] in
                                                                    let uu____25717
                                                                    =
                                                                    let uu____25718
                                                                    =
                                                                    let uu____25723
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25724
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25723,
                                                                    uu____25724) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25718 in
                                                                    (uu____25704,
                                                                    [x],
                                                                    uu____25717) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25693 in
                                                                    let uu____25743
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25692,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25743) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25685
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25750
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
                                                                    (let uu____25778
                                                                    =
                                                                    let uu____25779
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25779
                                                                    dapp1 in
                                                                    [uu____25778]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25750
                                                                    FStar_List.flatten in
                                                                    let uu____25786
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    let uu____25794
                                                                    =
                                                                    let uu____25805
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25816
                                                                    =
                                                                    let uu____25817
                                                                    =
                                                                    let uu____25822
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25822) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25817 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25805,
                                                                    uu____25816) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25794 in
                                                                    (uu____25793,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25786) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25841 ->
                                                        ((let uu____25843 =
                                                            let uu____25844 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25845 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25844
                                                              uu____25845 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25843);
                                                         ([], []))) in
                                             let uu____25850 = encode_elim () in
                                             (match uu____25850 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25870 =
                                                      let uu____25873 =
                                                        let uu____25876 =
                                                          let uu____25879 =
                                                            let uu____25882 =
                                                              let uu____25883
                                                                =
                                                                let uu____25894
                                                                  =
                                                                  let uu____25897
                                                                    =
                                                                    let uu____25898
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25898 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25897 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25894) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25883 in
                                                            [uu____25882] in
                                                          let uu____25903 =
                                                            let uu____25906 =
                                                              let uu____25909
                                                                =
                                                                let uu____25912
                                                                  =
                                                                  let uu____25915
                                                                    =
                                                                    let uu____25918
                                                                    =
                                                                    let uu____25921
                                                                    =
                                                                    let uu____25922
                                                                    =
                                                                    let uu____25929
                                                                    =
                                                                    let uu____25930
                                                                    =
                                                                    let uu____25941
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25941) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25930 in
                                                                    (uu____25929,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25922 in
                                                                    let uu____25954
                                                                    =
                                                                    let uu____25957
                                                                    =
                                                                    let uu____25958
                                                                    =
                                                                    let uu____25965
                                                                    =
                                                                    let uu____25966
                                                                    =
                                                                    let uu____25977
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25988
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25977,
                                                                    uu____25988) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25966 in
                                                                    (uu____25965,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25958 in
                                                                    [uu____25957] in
                                                                    uu____25921
                                                                    ::
                                                                    uu____25954 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25918 in
                                                                  FStar_List.append
                                                                    uu____25915
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25912 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25909 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25906 in
                                                          FStar_List.append
                                                            uu____25879
                                                            uu____25903 in
                                                        FStar_List.append
                                                          decls3 uu____25876 in
                                                      FStar_List.append
                                                        decls2 uu____25873 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25870 in
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
           (fun uu____26034  ->
              fun se  ->
                match uu____26034 with
                | (g,env1) ->
                    let uu____26054 = encode_sigelt env1 se in
                    (match uu____26054 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26113 =
        match uu____26113 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26145 ->
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
                 ((let uu____26151 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26151
                   then
                     let uu____26152 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26153 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26154 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26152 uu____26153 uu____26154
                   else ());
                  (let uu____26156 = encode_term t1 env1 in
                   match uu____26156 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26172 =
                         let uu____26179 =
                           let uu____26180 =
                             let uu____26181 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26181
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26180 in
                         new_term_constant_from_string env1 x uu____26179 in
                       (match uu____26172 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26197 = FStar_Options.log_queries () in
                              if uu____26197
                              then
                                let uu____26200 =
                                  let uu____26201 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26202 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26203 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26201 uu____26202 uu____26203 in
                                FStar_Pervasives_Native.Some uu____26200
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26219,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26233 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26233 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26256,se,uu____26258) ->
                 let uu____26263 = encode_sigelt env1 se in
                 (match uu____26263 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26280,se) ->
                 let uu____26286 = encode_sigelt env1 se in
                 (match uu____26286 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26303 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26303 with | (uu____26326,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26341 'Auu____26342 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26342,'Auu____26341)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26410  ->
              match uu____26410 with
              | (l,uu____26422,uu____26423) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26469  ->
              match uu____26469 with
              | (l,uu____26483,uu____26484) ->
                  let uu____26493 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26494 =
                    let uu____26497 =
                      let uu____26498 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26498 in
                    [uu____26497] in
                  uu____26493 :: uu____26494)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26520 =
      let uu____26523 =
        let uu____26524 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26527 =
          let uu____26528 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26528 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26524;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26527
        } in
      [uu____26523] in
    FStar_ST.op_Colon_Equals last_env uu____26520
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26555 = FStar_ST.op_Bang last_env in
      match uu____26555 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26577 ->
          let uu___161_26580 = e in
          let uu____26581 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_26580.bindings);
            depth = (uu___161_26580.depth);
            tcenv;
            warn = (uu___161_26580.warn);
            cache = (uu___161_26580.cache);
            nolabels = (uu___161_26580.nolabels);
            use_zfuel_name = (uu___161_26580.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_26580.encode_non_total_function_typ);
            current_module_name = uu____26581
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26586 = FStar_ST.op_Bang last_env in
    match uu____26586 with
    | [] -> failwith "Empty env stack"
    | uu____26607::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26632  ->
    let uu____26633 = FStar_ST.op_Bang last_env in
    match uu____26633 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_26662 = hd1 in
          {
            bindings = (uu___162_26662.bindings);
            depth = (uu___162_26662.depth);
            tcenv = (uu___162_26662.tcenv);
            warn = (uu___162_26662.warn);
            cache = refs;
            nolabels = (uu___162_26662.nolabels);
            use_zfuel_name = (uu___162_26662.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_26662.encode_non_total_function_typ);
            current_module_name = (uu___162_26662.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26684  ->
    let uu____26685 = FStar_ST.op_Bang last_env in
    match uu____26685 with
    | [] -> failwith "Popping an empty stack"
    | uu____26706::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____26731  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____26735  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____26739  ->
    let uu____26740 = FStar_ST.op_Bang last_env in
    match uu____26740 with
    | hd1::uu____26762::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26784 -> failwith "Impossible"
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
        | (uu____26849::uu____26850,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___163_26858 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___163_26858.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___163_26858.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___163_26858.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26859 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26876 =
        let uu____26879 =
          let uu____26880 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26880 in
        let uu____26881 = open_fact_db_tags env in uu____26879 :: uu____26881 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26876
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
      let uu____26905 = encode_sigelt env se in
      match uu____26905 with
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
        let uu____26943 = FStar_Options.log_queries () in
        if uu____26943
        then
          let uu____26946 =
            let uu____26947 =
              let uu____26948 =
                let uu____26949 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26949 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26948 in
            FStar_SMTEncoding_Term.Caption uu____26947 in
          uu____26946 :: decls
        else decls in
      let env =
        let uu____26960 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26960 tcenv in
      let uu____26961 = encode_top_level_facts env se in
      match uu____26961 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26975 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26975))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26989 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26989
       then
         let uu____26990 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26990
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27025  ->
                 fun se  ->
                   match uu____27025 with
                   | (g,env2) ->
                       let uu____27045 = encode_top_level_facts env2 se in
                       (match uu____27045 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27068 =
         encode_signature
           (let uu___164_27077 = env in
            {
              bindings = (uu___164_27077.bindings);
              depth = (uu___164_27077.depth);
              tcenv = (uu___164_27077.tcenv);
              warn = false;
              cache = (uu___164_27077.cache);
              nolabels = (uu___164_27077.nolabels);
              use_zfuel_name = (uu___164_27077.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___164_27077.encode_non_total_function_typ);
              current_module_name = (uu___164_27077.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27068 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27094 = FStar_Options.log_queries () in
             if uu____27094
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___165_27102 = env1 in
               {
                 bindings = (uu___165_27102.bindings);
                 depth = (uu___165_27102.depth);
                 tcenv = (uu___165_27102.tcenv);
                 warn = true;
                 cache = (uu___165_27102.cache);
                 nolabels = (uu___165_27102.nolabels);
                 use_zfuel_name = (uu___165_27102.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___165_27102.encode_non_total_function_typ);
                 current_module_name = (uu___165_27102.current_module_name)
               });
            (let uu____27104 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27104
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
        (let uu____27159 =
           let uu____27160 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27160.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27159);
        (let env =
           let uu____27162 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27162 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27174 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27209 = aux rest in
                 (match uu____27209 with
                  | (out,rest1) ->
                      let t =
                        let uu____27239 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27239 with
                        | FStar_Pervasives_Native.Some uu____27244 ->
                            let uu____27245 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27245
                              x.FStar_Syntax_Syntax.sort
                        | uu____27246 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27250 =
                        let uu____27253 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___166_27256 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_27256.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_27256.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27253 :: out in
                      (uu____27250, rest1))
             | uu____27261 -> ([], bindings1) in
           let uu____27268 = aux bindings in
           match uu____27268 with
           | (closing,bindings1) ->
               let uu____27293 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27293, bindings1) in
         match uu____27174 with
         | (q1,bindings1) ->
             let uu____27316 =
               let uu____27321 =
                 FStar_List.filter
                   (fun uu___131_27326  ->
                      match uu___131_27326 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27327 ->
                          false
                      | uu____27334 -> true) bindings1 in
               encode_env_bindings env uu____27321 in
             (match uu____27316 with
              | (env_decls,env1) ->
                  ((let uu____27352 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27352
                    then
                      let uu____27353 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27353
                    else ());
                   (let uu____27355 = encode_formula q1 env1 in
                    match uu____27355 with
                    | (phi,qdecls) ->
                        let uu____27376 =
                          let uu____27381 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27381 phi in
                        (match uu____27376 with
                         | (labels,phi1) ->
                             let uu____27398 = encode_labels labels in
                             (match uu____27398 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27435 =
                                      let uu____27442 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27443 =
                                        varops.mk_unique "@query" in
                                      (uu____27442,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27443) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27435 in
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
        let uu____27462 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27462 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27464 = encode_formula q env in
       match uu____27464 with
       | (f,uu____27470) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27472) -> true
             | uu____27477 -> false)))