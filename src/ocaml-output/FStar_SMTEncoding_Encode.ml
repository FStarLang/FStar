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
      (fun uu___102_119  ->
         match uu___102_119 with
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
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___126_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_221.FStar_Syntax_Syntax.sort)
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
    let uu___127_2159 = x in
    let uu____2160 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____2160;
      FStar_Syntax_Syntax.index = (uu___127_2159.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_2159.FStar_Syntax_Syntax.sort)
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
                 (fun uu___103_2632  ->
                    match uu___103_2632 with
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
           (fun uu___104_2657  ->
              match uu___104_2657 with
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
        (let uu___128_2746 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_2746.tcenv);
           warn = (uu___128_2746.warn);
           cache = (uu___128_2746.cache);
           nolabels = (uu___128_2746.nolabels);
           use_zfuel_name = (uu___128_2746.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_2746.encode_non_total_function_typ);
           current_module_name = (uu___128_2746.current_module_name)
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
        (let uu___129_2766 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_2766.depth);
           tcenv = (uu___129_2766.tcenv);
           warn = (uu___129_2766.warn);
           cache = (uu___129_2766.cache);
           nolabels = (uu___129_2766.nolabels);
           use_zfuel_name = (uu___129_2766.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_2766.encode_non_total_function_typ);
           current_module_name = (uu___129_2766.current_module_name)
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
          (let uu___130_2790 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_2790.depth);
             tcenv = (uu___130_2790.tcenv);
             warn = (uu___130_2790.warn);
             cache = (uu___130_2790.cache);
             nolabels = (uu___130_2790.nolabels);
             use_zfuel_name = (uu___130_2790.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_2790.encode_non_total_function_typ);
             current_module_name = (uu___130_2790.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_2803 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_2803.depth);
          tcenv = (uu___131_2803.tcenv);
          warn = (uu___131_2803.warn);
          cache = (uu___131_2803.cache);
          nolabels = (uu___131_2803.nolabels);
          use_zfuel_name = (uu___131_2803.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_2803.encode_non_total_function_typ);
          current_module_name = (uu___131_2803.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_2829  ->
             match uu___105_2829 with
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
        let uu___132_2902 = env in
        let uu____2903 =
          let uu____2906 =
            let uu____2907 =
              let uu____2920 =
                let uu____2923 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                  uu____2923 in
              (x, fname, uu____2920, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2907 in
          uu____2906 :: (env.bindings) in
        {
          bindings = uu____2903;
          depth = (uu___132_2902.depth);
          tcenv = (uu___132_2902.tcenv);
          warn = (uu___132_2902.warn);
          cache = (uu___132_2902.cache);
          nolabels = (uu___132_2902.nolabels);
          use_zfuel_name = (uu___132_2902.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_2902.encode_non_total_function_typ);
          current_module_name = (uu___132_2902.current_module_name)
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
        (fun uu___106_2967  ->
           match uu___106_2967 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____3006 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____3025 =
        lookup_binding env
          (fun uu___107_3033  ->
             match uu___107_3033 with
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
          let uu___133_3155 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_3155.depth);
            tcenv = (uu___133_3155.tcenv);
            warn = (uu___133_3155.warn);
            cache = (uu___133_3155.cache);
            nolabels = (uu___133_3155.nolabels);
            use_zfuel_name = (uu___133_3155.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_3155.encode_non_total_function_typ);
            current_module_name = (uu___133_3155.current_module_name)
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
            let uu___134_3210 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_3210.depth);
              tcenv = (uu___134_3210.tcenv);
              warn = (uu___134_3210.warn);
              cache = (uu___134_3210.cache);
              nolabels = (uu___134_3210.nolabels);
              use_zfuel_name = (uu___134_3210.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_3210.encode_non_total_function_typ);
              current_module_name = (uu___134_3210.current_module_name)
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
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
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
        (fun uu___108_3464  ->
           match uu___108_3464 with
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
               (fun uu___109_3791  ->
                  match uu___109_3791 with
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
  fun uu___110_3899  ->
    match uu___110_3899 with
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
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_4233  ->
    match uu___111_4233 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____4235 =
          let uu____4242 =
            let uu____4245 =
              let uu____4246 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____4246 in
            [uu____4245] in
          ("FStar.Char.Char", uu____4242) in
        FStar_SMTEncoding_Util.mkApp uu____4235
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____4260 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____4260
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4262) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____4278) ->
        let uu____4283 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____4283
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4288 =
          let uu____4289 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____4289 in
        failwith uu____4288
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4310 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4323 ->
            let uu____4330 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4330
        | uu____4331 ->
            if norm1
            then let uu____4332 = whnf env t1 in aux false uu____4332
            else
              (let uu____4334 =
                 let uu____4335 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4336 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4335 uu____4336 in
               failwith uu____4334) in
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
    | uu____4368 ->
        let uu____4369 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4369)
let is_arithmetic_primitive:
  'Auu____4386 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4386 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4406::uu____4407::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4411::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4414 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4436 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4452 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4459 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4459)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4498)::uu____4499::uu____4500::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4551)::uu____4552::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4589 -> false
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
        (let uu____4798 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4798
         then
           let uu____4799 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4799
         else ());
        (let uu____4801 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4885  ->
                   fun b  ->
                     match uu____4885 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4964 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4980 = gen_term_var env1 x in
                           match uu____4980 with
                           | (xxsym,xx,env') ->
                               let uu____5004 =
                                 let uu____5009 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____5009 env1 xx in
                               (match uu____5004 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4964 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4801 with
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
          let uu____5168 = encode_term t env in
          match uu____5168 with
          | (t1,decls) ->
              let uu____5179 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____5179, decls)
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
          let uu____5190 = encode_term t env in
          match uu____5190 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5205 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____5205, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5207 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____5207, decls))
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
        let uu____5213 = encode_args args_e env in
        match uu____5213 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5232 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5241 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5241 in
            let binary arg_tms1 =
              let uu____5254 =
                let uu____5255 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5255 in
              let uu____5256 =
                let uu____5257 =
                  let uu____5258 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5258 in
                FStar_SMTEncoding_Term.unboxInt uu____5257 in
              (uu____5254, uu____5256) in
            let mk_default uu____5264 =
              let uu____5265 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5265 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5316 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5316
              then
                let uu____5317 = let uu____5318 = mk_args ts in op uu____5318 in
                FStar_All.pipe_right uu____5317 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5347 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5347
              then
                let uu____5348 = binary ts in
                match uu____5348 with
                | (t1,t2) ->
                    let uu____5355 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5355
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5359 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5359
                 then
                   let uu____5360 = op (binary ts) in
                   FStar_All.pipe_right uu____5360
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
            let uu____5491 =
              let uu____5500 =
                FStar_List.tryFind
                  (fun uu____5522  ->
                     match uu____5522 with
                     | (l,uu____5532) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5500 FStar_Util.must in
            (match uu____5491 with
             | (uu____5571,op) ->
                 let uu____5581 = op arg_tms in (uu____5581, decls))
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
        let uu____5589 = FStar_List.hd args_e in
        match uu____5589 with
        | (tm_sz,uu____5597) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5607 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5607 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5615 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5615);
                   t_decls) in
            let uu____5616 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5636::(sz_arg,uu____5638)::uu____5639::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5688 =
                    let uu____5691 = FStar_List.tail args_e in
                    FStar_List.tail uu____5691 in
                  let uu____5694 =
                    let uu____5697 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5697 in
                  (uu____5688, uu____5694)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5703::(sz_arg,uu____5705)::uu____5706::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5755 =
                    let uu____5756 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5756 in
                  failwith uu____5755
              | uu____5765 ->
                  let uu____5772 = FStar_List.tail args_e in
                  (uu____5772, FStar_Pervasives_Native.None) in
            (match uu____5616 with
             | (arg_tms,ext_sz) ->
                 let uu____5795 = encode_args arg_tms env in
                 (match uu____5795 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5816 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5825 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5825 in
                      let unary_arith arg_tms2 =
                        let uu____5834 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5834 in
                      let binary arg_tms2 =
                        let uu____5847 =
                          let uu____5848 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5848 in
                        let uu____5849 =
                          let uu____5850 =
                            let uu____5851 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5851 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5850 in
                        (uu____5847, uu____5849) in
                      let binary_arith arg_tms2 =
                        let uu____5866 =
                          let uu____5867 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5867 in
                        let uu____5868 =
                          let uu____5869 =
                            let uu____5870 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5870 in
                          FStar_SMTEncoding_Term.unboxInt uu____5869 in
                        (uu____5866, uu____5868) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5919 =
                          let uu____5920 = mk_args ts in op uu____5920 in
                        FStar_All.pipe_right uu____5919 resBox in
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
                        let uu____6010 =
                          let uu____6013 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____6013 in
                        let uu____6015 =
                          let uu____6018 =
                            let uu____6019 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____6019 in
                          FStar_SMTEncoding_Term.boxBitVec uu____6018 in
                        mk_bv uu____6010 unary uu____6015 arg_tms2 in
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
                      let uu____6194 =
                        let uu____6203 =
                          FStar_List.tryFind
                            (fun uu____6225  ->
                               match uu____6225 with
                               | (l,uu____6235) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6203 FStar_Util.must in
                      (match uu____6194 with
                       | (uu____6276,op) ->
                           let uu____6286 = op arg_tms1 in
                           (uu____6286, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6297 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6297
       then
         let uu____6298 = FStar_Syntax_Print.tag_of_term t in
         let uu____6299 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6300 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6298 uu____6299
           uu____6300
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6306 ->
           let uu____6331 =
             let uu____6332 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6333 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6334 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6335 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6332
               uu____6333 uu____6334 uu____6335 in
           failwith uu____6331
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6340 =
             let uu____6341 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6342 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6343 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6344 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6341
               uu____6342 uu____6343 uu____6344 in
           failwith uu____6340
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6350 =
             let uu____6351 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6351 in
           failwith uu____6350
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6358) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6400) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6410 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6410, [])
       | FStar_Syntax_Syntax.Tm_type uu____6413 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6417) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6423 = encode_const c in (uu____6423, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6445 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6445 with
            | (binders1,res) ->
                let uu____6456 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6456
                then
                  let uu____6461 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6461 with
                   | (vars,guards,env',decls,uu____6486) ->
                       let fsym =
                         let uu____6504 = varops.fresh "f" in
                         (uu____6504, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6507 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_6516 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_6516.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_6516.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_6516.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_6516.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_6516.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_6516.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_6516.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_6516.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_6516.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_6516.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_6516.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_6516.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_6516.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_6516.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_6516.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_6516.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_6516.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_6516.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_6516.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_6516.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_6516.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_6516.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_6516.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_6516.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_6516.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_6516.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____6507 with
                        | (pre_opt,res_t) ->
                            let uu____6527 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6527 with
                             | (res_pred,decls') ->
                                 let uu____6538 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6551 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6551, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6555 =
                                         encode_formula pre env' in
                                       (match uu____6555 with
                                        | (guard,decls0) ->
                                            let uu____6568 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6568, decls0)) in
                                 (match uu____6538 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6580 =
                                          let uu____6591 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6591) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6580 in
                                      let cvars =
                                        let uu____6609 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6609
                                          (FStar_List.filter
                                             (fun uu____6623  ->
                                                match uu____6623 with
                                                | (x,uu____6629) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6648 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6648 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6656 =
                                             let uu____6657 =
                                               let uu____6664 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6664) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6657 in
                                           (uu____6656,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6684 =
                                               let uu____6685 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6685 in
                                             varops.mk_unique uu____6684 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6696 =
                                               FStar_Options.log_queries () in
                                             if uu____6696
                                             then
                                               let uu____6699 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6699
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6707 =
                                               let uu____6714 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6714) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6707 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6726 =
                                               let uu____6733 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6733,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6726 in
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
                                             let uu____6754 =
                                               let uu____6761 =
                                                 let uu____6762 =
                                                   let uu____6773 =
                                                     let uu____6774 =
                                                       let uu____6779 =
                                                         let uu____6780 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6780 in
                                                       (f_has_t, uu____6779) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6774 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6773) in
                                                 mkForall_fuel uu____6762 in
                                               (uu____6761,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6754 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6803 =
                                               let uu____6810 =
                                                 let uu____6811 =
                                                   let uu____6822 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6822) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6811 in
                                               (uu____6810,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6803 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6847 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6847);
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
                     let uu____6862 =
                       let uu____6869 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6869,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6862 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6881 =
                       let uu____6888 =
                         let uu____6889 =
                           let uu____6900 =
                             let uu____6901 =
                               let uu____6906 =
                                 let uu____6907 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6907 in
                               (f_has_t, uu____6906) in
                             FStar_SMTEncoding_Util.mkImp uu____6901 in
                           ([[f_has_t]], [fsym], uu____6900) in
                         mkForall_fuel uu____6889 in
                       (uu____6888, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6881 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6934 ->
           let uu____6941 =
             let uu____6946 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6946 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6953;
                 FStar_Syntax_Syntax.vars = uu____6954;_} ->
                 let uu____6961 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6961 with
                  | (b,f1) ->
                      let uu____6986 =
                        let uu____6987 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6987 in
                      (uu____6986, f1))
             | uu____6996 -> failwith "impossible" in
           (match uu____6941 with
            | (x,f) ->
                let uu____7007 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____7007 with
                 | (base_t,decls) ->
                     let uu____7018 = gen_term_var env x in
                     (match uu____7018 with
                      | (x1,xtm,env') ->
                          let uu____7032 = encode_formula f env' in
                          (match uu____7032 with
                           | (refinement,decls') ->
                               let uu____7043 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____7043 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____7059 =
                                        let uu____7062 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____7069 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____7062
                                          uu____7069 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7059 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7102  ->
                                              match uu____7102 with
                                              | (y,uu____7108) ->
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
                                    let uu____7141 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7141 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7149 =
                                           let uu____7150 =
                                             let uu____7157 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7157) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7150 in
                                         (uu____7149,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7178 =
                                             let uu____7179 =
                                               let uu____7180 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7180 in
                                             Prims.strcat module_name
                                               uu____7179 in
                                           varops.mk_unique uu____7178 in
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
                                           let uu____7194 =
                                             let uu____7201 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7201) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7194 in
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
                                           let uu____7216 =
                                             let uu____7223 =
                                               let uu____7224 =
                                                 let uu____7235 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7235) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7224 in
                                             (uu____7223,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7216 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7261 =
                                             let uu____7268 =
                                               let uu____7269 =
                                                 let uu____7280 =
                                                   let uu____7281 =
                                                     let uu____7286 =
                                                       let uu____7287 =
                                                         let uu____7298 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7298) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7287 in
                                                     (uu____7286, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7281 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7280) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7269 in
                                             (uu____7268,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7261 in
                                         let t_kinding =
                                           let uu____7336 =
                                             let uu____7343 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7343,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7336 in
                                         let t_interp =
                                           let uu____7361 =
                                             let uu____7368 =
                                               let uu____7369 =
                                                 let uu____7380 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7380) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7369 in
                                             let uu____7403 =
                                               let uu____7406 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7406 in
                                             (uu____7368, uu____7403,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7361 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7413 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7413);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7443 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7443 in
           let uu____7444 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7444 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7456 =
                    let uu____7463 =
                      let uu____7464 =
                        let uu____7465 =
                          let uu____7466 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7466 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7465 in
                      varops.mk_unique uu____7464 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7463) in
                  FStar_SMTEncoding_Util.mkAssume uu____7456 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7471 ->
           let uu____7486 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7486 with
            | (head1,args_e) ->
                let uu____7527 =
                  let uu____7540 =
                    let uu____7541 = FStar_Syntax_Subst.compress head1 in
                    uu____7541.FStar_Syntax_Syntax.n in
                  (uu____7540, args_e) in
                (match uu____7527 with
                 | uu____7556 when head_redex env head1 ->
                     let uu____7569 = whnf env t in
                     encode_term uu____7569 env
                 | uu____7570 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7589 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7603;
                       FStar_Syntax_Syntax.vars = uu____7604;_},uu____7605),uu____7606::
                    (v1,uu____7608)::(v2,uu____7610)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7661 = encode_term v1 env in
                     (match uu____7661 with
                      | (v11,decls1) ->
                          let uu____7672 = encode_term v2 env in
                          (match uu____7672 with
                           | (v21,decls2) ->
                               let uu____7683 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7683,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7687::(v1,uu____7689)::(v2,uu____7691)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7738 = encode_term v1 env in
                     (match uu____7738 with
                      | (v11,decls1) ->
                          let uu____7749 = encode_term v2 env in
                          (match uu____7749 with
                           | (v21,decls2) ->
                               let uu____7760 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7760,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7763) ->
                     let e0 =
                       let uu____7781 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7781 in
                     ((let uu____7789 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7789
                       then
                         let uu____7790 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7790
                       else ());
                      (let e =
                         let uu____7795 =
                           let uu____7796 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7797 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7796
                             uu____7797 in
                         uu____7795 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7806),(arg,uu____7808)::[]) -> encode_term arg env
                 | uu____7833 ->
                     let uu____7846 = encode_args args_e env in
                     (match uu____7846 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7901 = encode_term head1 env in
                            match uu____7901 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7965 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7965 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8043  ->
                                                 fun uu____8044  ->
                                                   match (uu____8043,
                                                           uu____8044)
                                                   with
                                                   | ((bv,uu____8066),
                                                      (a,uu____8068)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____8086 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____8086
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____8091 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____8091 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____8106 =
                                                   let uu____8113 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____8122 =
                                                     let uu____8123 =
                                                       let uu____8124 =
                                                         let uu____8125 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____8125 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8124 in
                                                     varops.mk_unique
                                                       uu____8123 in
                                                   (uu____8113,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8122) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8106 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____8142 = lookup_free_var_sym env fv in
                            match uu____8142 with
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
                                   FStar_Syntax_Syntax.pos = uu____8173;
                                   FStar_Syntax_Syntax.vars = uu____8174;_},uu____8175)
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
                                   FStar_Syntax_Syntax.pos = uu____8186;
                                   FStar_Syntax_Syntax.vars = uu____8187;_},uu____8188)
                                ->
                                let uu____8193 =
                                  let uu____8194 =
                                    let uu____8199 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8199
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8194
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8193
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8229 =
                                  let uu____8230 =
                                    let uu____8235 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8235
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8230
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8229
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8264,(FStar_Util.Inl t1,uu____8266),uu____8267)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8316,(FStar_Util.Inr c,uu____8318),uu____8319)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8368 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8395 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8395 in
                               let uu____8396 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8396 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8412;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8413;_},uu____8414)
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
                                     | uu____8428 ->
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
           let uu____8477 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8477 with
            | (bs1,body1,opening) ->
                let fallback uu____8500 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8507 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8507, [decl]) in
                let is_impure rc =
                  let uu____8514 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8514 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8524 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8524
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8544 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8544
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8548 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8548)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8555 =
                         let uu____8556 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8556 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8555);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8558 =
                       (is_impure rc) &&
                         (let uu____8560 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8560) in
                     if uu____8558
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8567 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8567 with
                        | (vars,guards,envbody,decls,uu____8592) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
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
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____8952 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____8952, [decl_e])))
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
              let uu____9007 = encode_term e1 env in
              match uu____9007 with
              | (ee1,decls1) ->
                  let uu____9018 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9018 with
                   | (xs,e21) ->
                       let uu____9043 = FStar_List.hd xs in
                       (match uu____9043 with
                        | (x1,uu____9057) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9059 = encode_body e21 env' in
                            (match uu____9059 with
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
            let uu____9091 =
              let uu____9098 =
                let uu____9099 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9099 in
              gen_term_var env uu____9098 in
            match uu____9091 with
            | (scrsym,scr',env1) ->
                let uu____9107 = encode_term e env1 in
                (match uu____9107 with
                 | (scr,decls) ->
                     let uu____9118 =
                       let encode_branch b uu____9143 =
                         match uu____9143 with
                         | (else_case,decls1) ->
                             let uu____9162 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9162 with
                              | (p,w,br) ->
                                  let uu____9188 = encode_pat env1 p in
                                  (match uu____9188 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9225  ->
                                                   match uu____9225 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9232 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9254 =
                                               encode_term w1 env2 in
                                             (match uu____9254 with
                                              | (w2,decls2) ->
                                                  let uu____9267 =
                                                    let uu____9268 =
                                                      let uu____9273 =
                                                        let uu____9274 =
                                                          let uu____9279 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9279) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9274 in
                                                      (guard, uu____9273) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9268 in
                                                  (uu____9267, decls2)) in
                                       (match uu____9232 with
                                        | (guard1,decls2) ->
                                            let uu____9292 =
                                              encode_br br env2 in
                                            (match uu____9292 with
                                             | (br1,decls3) ->
                                                 let uu____9305 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9305,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9118 with
                      | (match_tm,decls1) ->
                          let uu____9324 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9324, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9364 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9364
       then
         let uu____9365 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9365
       else ());
      (let uu____9367 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9367 with
       | (vars,pat_term) ->
           let uu____9384 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9437  ->
                     fun v1  ->
                       match uu____9437 with
                       | (env1,vars1) ->
                           let uu____9489 = gen_term_var env1 v1 in
                           (match uu____9489 with
                            | (xx,uu____9511,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9384 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9590 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9591 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9592 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9600 =
                        let uu____9605 = encode_const c in
                        (scrutinee, uu____9605) in
                      FStar_SMTEncoding_Util.mkEq uu____9600
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9626 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9626 with
                        | (uu____9633,uu____9634::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9637 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9670  ->
                                  match uu____9670 with
                                  | (arg,uu____9678) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9684 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9684)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9711) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9742 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9765 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9809  ->
                                  match uu____9809 with
                                  | (arg,uu____9823) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9829 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9829)) in
                      FStar_All.pipe_right uu____9765 FStar_List.flatten in
                let pat_term1 uu____9857 = encode_term pat_term env1 in
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
      let uu____9867 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9905  ->
                fun uu____9906  ->
                  match (uu____9905, uu____9906) with
                  | ((tms,decls),(t,uu____9942)) ->
                      let uu____9963 = encode_term t env in
                      (match uu____9963 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9867 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10020 = FStar_Syntax_Util.list_elements e in
        match uu____10020 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____10041 =
          let uu____10056 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10056 FStar_Syntax_Util.head_and_args in
        match uu____10041 with
        | (head1,args) ->
            let uu____10095 =
              let uu____10108 =
                let uu____10109 = FStar_Syntax_Util.un_uinst head1 in
                uu____10109.FStar_Syntax_Syntax.n in
              (uu____10108, args) in
            (match uu____10095 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10123,uu____10124)::(e,uu____10126)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10161 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10197 =
            let uu____10212 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10212 FStar_Syntax_Util.head_and_args in
          match uu____10197 with
          | (head1,args) ->
              let uu____10253 =
                let uu____10266 =
                  let uu____10267 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10267.FStar_Syntax_Syntax.n in
                (uu____10266, args) in
              (match uu____10253 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10284)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10311 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10333 = smt_pat_or1 t1 in
            (match uu____10333 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10349 = list_elements1 e in
                 FStar_All.pipe_right uu____10349
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10367 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10367
                           (FStar_List.map one_pat)))
             | uu____10378 ->
                 let uu____10383 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10383])
        | uu____10404 ->
            let uu____10407 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10407] in
      let uu____10428 =
        let uu____10447 =
          let uu____10448 = FStar_Syntax_Subst.compress t in
          uu____10448.FStar_Syntax_Syntax.n in
        match uu____10447 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10487 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10487 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10530;
                        FStar_Syntax_Syntax.effect_name = uu____10531;
                        FStar_Syntax_Syntax.result_typ = uu____10532;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10534)::(post,uu____10536)::(pats,uu____10538)::[];
                        FStar_Syntax_Syntax.flags = uu____10539;_}
                      ->
                      let uu____10580 = lemma_pats pats in
                      (binders1, pre, post, uu____10580)
                  | uu____10597 -> failwith "impos"))
        | uu____10616 -> failwith "Impos" in
      match uu____10428 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_10664 = env in
            {
              bindings = (uu___136_10664.bindings);
              depth = (uu___136_10664.depth);
              tcenv = (uu___136_10664.tcenv);
              warn = (uu___136_10664.warn);
              cache = (uu___136_10664.cache);
              nolabels = (uu___136_10664.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_10664.encode_non_total_function_typ);
              current_module_name = (uu___136_10664.current_module_name)
            } in
          let uu____10665 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10665 with
           | (vars,guards,env2,decls,uu____10690) ->
               let uu____10703 =
                 let uu____10716 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10760 =
                             let uu____10769 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10769
                               FStar_List.unzip in
                           match uu____10760 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10716 FStar_List.unzip in
               (match uu____10703 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_10878 = env2 in
                      {
                        bindings = (uu___137_10878.bindings);
                        depth = (uu___137_10878.depth);
                        tcenv = (uu___137_10878.tcenv);
                        warn = (uu___137_10878.warn);
                        cache = (uu___137_10878.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_10878.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_10878.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_10878.current_module_name)
                      } in
                    let uu____10879 =
                      let uu____10884 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10884 env3 in
                    (match uu____10879 with
                     | (pre1,decls'') ->
                         let uu____10891 =
                           let uu____10896 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10896 env3 in
                         (match uu____10891 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10906 =
                                let uu____10907 =
                                  let uu____10918 =
                                    let uu____10919 =
                                      let uu____10924 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10924, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10919 in
                                  (pats, vars, uu____10918) in
                                FStar_SMTEncoding_Util.mkForall uu____10907 in
                              (uu____10906, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10943 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10943
        then
          let uu____10944 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10945 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10944 uu____10945
        else () in
      let enc f r l =
        let uu____10978 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11006 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11006 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10978 with
        | (decls,args) ->
            let uu____11035 =
              let uu___138_11036 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_11036.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_11036.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11035, decls) in
      let const_op f r uu____11067 =
        let uu____11080 = f r in (uu____11080, []) in
      let un_op f l =
        let uu____11099 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11099 in
      let bin_op f uu___112_11115 =
        match uu___112_11115 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11126 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11160 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11183  ->
                 match uu____11183 with
                 | (t,uu____11197) ->
                     let uu____11198 = encode_formula t env in
                     (match uu____11198 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11160 with
        | (decls,phis) ->
            let uu____11227 =
              let uu___139_11228 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_11228.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_11228.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11227, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11289  ->
               match uu____11289 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11308) -> false
                    | uu____11309 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11324 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11324
        else
          (let uu____11338 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11338 r rf) in
      let mk_imp1 r uu___113_11363 =
        match uu___113_11363 with
        | (lhs,uu____11369)::(rhs,uu____11371)::[] ->
            let uu____11398 = encode_formula rhs env in
            (match uu____11398 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11413) ->
                      (l1, decls1)
                  | uu____11418 ->
                      let uu____11419 = encode_formula lhs env in
                      (match uu____11419 with
                       | (l2,decls2) ->
                           let uu____11430 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11430, (FStar_List.append decls1 decls2)))))
        | uu____11433 -> failwith "impossible" in
      let mk_ite r uu___114_11454 =
        match uu___114_11454 with
        | (guard,uu____11460)::(_then,uu____11462)::(_else,uu____11464)::[]
            ->
            let uu____11501 = encode_formula guard env in
            (match uu____11501 with
             | (g,decls1) ->
                 let uu____11512 = encode_formula _then env in
                 (match uu____11512 with
                  | (t,decls2) ->
                      let uu____11523 = encode_formula _else env in
                      (match uu____11523 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11537 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11562 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11562 in
      let connectives =
        let uu____11580 =
          let uu____11593 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11593) in
        let uu____11610 =
          let uu____11625 =
            let uu____11638 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11638) in
          let uu____11655 =
            let uu____11670 =
              let uu____11685 =
                let uu____11698 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11698) in
              let uu____11715 =
                let uu____11730 =
                  let uu____11745 =
                    let uu____11758 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11758) in
                  [uu____11745;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11730 in
              uu____11685 :: uu____11715 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11670 in
          uu____11625 :: uu____11655 in
        uu____11580 :: uu____11610 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12079 = encode_formula phi' env in
            (match uu____12079 with
             | (phi2,decls) ->
                 let uu____12090 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12090, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12091 ->
            let uu____12098 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12098 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12137 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12137 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12149;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12151;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12172 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12172 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12219::(x,uu____12221)::(t,uu____12223)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12270 = encode_term x env in
                 (match uu____12270 with
                  | (x1,decls) ->
                      let uu____12281 = encode_term t env in
                      (match uu____12281 with
                       | (t1,decls') ->
                           let uu____12292 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12292, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12297)::(msg,uu____12299)::(phi2,uu____12301)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12346 =
                   let uu____12351 =
                     let uu____12352 = FStar_Syntax_Subst.compress r in
                     uu____12352.FStar_Syntax_Syntax.n in
                   let uu____12355 =
                     let uu____12356 = FStar_Syntax_Subst.compress msg in
                     uu____12356.FStar_Syntax_Syntax.n in
                   (uu____12351, uu____12355) in
                 (match uu____12346 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12365))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
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
                          (let uu___140_12421 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_12421.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_12421.FStar_SMTEncoding_Term.freevars);
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
                     (let uu___141_12437 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_12437.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_12437.FStar_SMTEncoding_Term.freevars);
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
                                          (let uu___142_12637 = env2 in
                                           {
                                             bindings =
                                               (uu___142_12637.bindings);
                                             depth = (uu___142_12637.depth);
                                             tcenv = (uu___142_12637.tcenv);
                                             warn = (uu___142_12637.warn);
                                             cache = (uu___142_12637.cache);
                                             nolabels =
                                               (uu___142_12637.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_12637.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_12637.current_module_name)
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
    (FStar_Parser_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16819 =
            FStar_Util.find_opt
              (fun uu____16845  ->
                 match uu____16845 with
                 | (l,uu____16857) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16819 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16882,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16921 = encode_function_type_as_formula t env in
        match uu____16921 with
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
              let uu____16967 =
                ((let uu____16970 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16970) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16967
              then
                let uu____16977 = new_term_constant_and_tok_from_lid env lid in
                match uu____16977 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16996 =
                        let uu____16997 = FStar_Syntax_Subst.compress t_norm in
                        uu____16997.FStar_Syntax_Syntax.n in
                      match uu____16996 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17003) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17033  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17038 -> [] in
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
                (let uu____17052 = prims.is lid in
                 if uu____17052
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17060 = prims.mk lid vname in
                   match uu____17060 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17084 =
                      let uu____17095 = curried_arrow_formals_comp t_norm in
                      match uu____17095 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17113 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17113
                            then
                              let uu____17114 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___143_17117 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___143_17117.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___143_17117.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___143_17117.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___143_17117.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___143_17117.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___143_17117.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___143_17117.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___143_17117.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___143_17117.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___143_17117.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___143_17117.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___143_17117.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___143_17117.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___143_17117.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___143_17117.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___143_17117.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___143_17117.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___143_17117.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___143_17117.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___143_17117.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___143_17117.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___143_17117.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___143_17117.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___143_17117.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___143_17117.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___143_17117.FStar_TypeChecker_Env.is_native_tactic)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17114
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17129 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17129)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17084 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17174 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17174 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17195 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___115_17237  ->
                                       match uu___115_17237 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17241 =
                                             FStar_Util.prefix vars in
                                           (match uu____17241 with
                                            | (uu____17262,(xxsym,uu____17264))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17282 =
                                                  let uu____17283 =
                                                    let uu____17290 =
                                                      let uu____17291 =
                                                        let uu____17302 =
                                                          let uu____17303 =
                                                            let uu____17308 =
                                                              let uu____17309
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17309 in
                                                            (vapp,
                                                              uu____17308) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17303 in
                                                        ([[vapp]], vars,
                                                          uu____17302) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17291 in
                                                    (uu____17290,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17283 in
                                                [uu____17282])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17328 =
                                             FStar_Util.prefix vars in
                                           (match uu____17328 with
                                            | (uu____17349,(xxsym,uu____17351))
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
                                                let uu____17374 =
                                                  let uu____17375 =
                                                    let uu____17382 =
                                                      let uu____17383 =
                                                        let uu____17394 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17394) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17383 in
                                                    (uu____17382,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17375 in
                                                [uu____17374])
                                       | uu____17411 -> [])) in
                             let uu____17412 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17412 with
                              | (vars,guards,env',decls1,uu____17439) ->
                                  let uu____17452 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17461 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17461, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17463 =
                                          encode_formula p env' in
                                        (match uu____17463 with
                                         | (g,ds) ->
                                             let uu____17474 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17474,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17452 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17487 =
                                           let uu____17494 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17494) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17487 in
                                       let uu____17503 =
                                         let vname_decl =
                                           let uu____17511 =
                                             let uu____17522 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17532  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17522,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17511 in
                                         let uu____17541 =
                                           let env2 =
                                             let uu___144_17547 = env1 in
                                             {
                                               bindings =
                                                 (uu___144_17547.bindings);
                                               depth = (uu___144_17547.depth);
                                               tcenv = (uu___144_17547.tcenv);
                                               warn = (uu___144_17547.warn);
                                               cache = (uu___144_17547.cache);
                                               nolabels =
                                                 (uu___144_17547.nolabels);
                                               use_zfuel_name =
                                                 (uu___144_17547.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___144_17547.current_module_name)
                                             } in
                                           let uu____17548 =
                                             let uu____17549 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17549 in
                                           if uu____17548
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17541 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17564::uu____17565 ->
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
                                                     let uu____17605 =
                                                       let uu____17616 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17616) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17605 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17643 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17646 =
                                               match formals with
                                               | [] ->
                                                   let uu____17663 =
                                                     let uu____17664 =
                                                       let uu____17667 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17667 in
                                                     push_free_var env1 lid
                                                       vname uu____17664 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17663)
                                               | uu____17672 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17679 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17679 in
                                                   let name_tok_corr =
                                                     let uu____17681 =
                                                       let uu____17688 =
                                                         let uu____17689 =
                                                           let uu____17700 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17700) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17689 in
                                                       (uu____17688,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17681 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17646 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17503 with
                                        | (decls2,env2) ->
                                            let uu____17743 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17751 =
                                                encode_term res_t1 env' in
                                              match uu____17751 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17764 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17764, decls) in
                                            (match uu____17743 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17775 =
                                                     let uu____17782 =
                                                       let uu____17783 =
                                                         let uu____17794 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17794) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17783 in
                                                     (uu____17782,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17775 in
                                                 let freshness =
                                                   let uu____17810 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17810
                                                   then
                                                     let uu____17815 =
                                                       let uu____17816 =
                                                         let uu____17827 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17838 =
                                                           varops.next_id () in
                                                         (vname, uu____17827,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17838) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17816 in
                                                     let uu____17841 =
                                                       let uu____17844 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17844] in
                                                     uu____17815 ::
                                                       uu____17841
                                                   else [] in
                                                 let g =
                                                   let uu____17849 =
                                                     let uu____17852 =
                                                       let uu____17855 =
                                                         let uu____17858 =
                                                           let uu____17861 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17861 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17858 in
                                                       FStar_List.append
                                                         decls3 uu____17855 in
                                                     FStar_List.append decls2
                                                       uu____17852 in
                                                   FStar_List.append decls11
                                                     uu____17849 in
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
          let uu____17896 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17896 with
          | FStar_Pervasives_Native.None  ->
              let uu____17933 = encode_free_var false env x t t_norm [] in
              (match uu____17933 with
               | (decls,env1) ->
                   let uu____17960 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17960 with
                    | (n1,x',uu____17987) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18008) ->
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
            let uu____18068 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18068 with
            | (decls,env1) ->
                let uu____18087 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18087
                then
                  let uu____18094 =
                    let uu____18097 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18097 in
                  (uu____18094, env1)
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
             (fun uu____18152  ->
                fun lb  ->
                  match uu____18152 with
                  | (decls,env1) ->
                      let uu____18172 =
                        let uu____18179 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18179
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18172 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18201 = FStar_Syntax_Util.head_and_args t in
    match uu____18201 with
    | (hd1,args) ->
        let uu____18238 =
          let uu____18239 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18239.FStar_Syntax_Syntax.n in
        (match uu____18238 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18243,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18262 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18287  ->
      fun quals  ->
        match uu____18287 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18363 = FStar_Util.first_N nbinders formals in
              match uu____18363 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18444  ->
                         fun uu____18445  ->
                           match (uu____18444, uu____18445) with
                           | ((formal,uu____18463),(binder,uu____18465)) ->
                               let uu____18474 =
                                 let uu____18481 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18481) in
                               FStar_Syntax_Syntax.NT uu____18474) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18489 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18520  ->
                              match uu____18520 with
                              | (x,i) ->
                                  let uu____18531 =
                                    let uu___145_18532 = x in
                                    let uu____18533 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_18532.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_18532.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18533
                                    } in
                                  (uu____18531, i))) in
                    FStar_All.pipe_right uu____18489
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18551 =
                      let uu____18552 = FStar_Syntax_Subst.compress body in
                      let uu____18553 =
                        let uu____18554 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18554 in
                      FStar_Syntax_Syntax.extend_app_n uu____18552
                        uu____18553 in
                    uu____18551 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18615 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18615
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_18618 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_18618.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_18618.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_18618.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_18618.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_18618.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_18618.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_18618.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_18618.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_18618.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_18618.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_18618.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_18618.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_18618.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_18618.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_18618.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_18618.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_18618.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_18618.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_18618.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_18618.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_18618.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_18618.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_18618.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_18618.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_18618.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_18618.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18651 = FStar_Syntax_Util.abs_formals e in
                match uu____18651 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18715::uu____18716 ->
                         let uu____18731 =
                           let uu____18732 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18732.FStar_Syntax_Syntax.n in
                         (match uu____18731 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18777 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18777 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18819 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18819
                                   then
                                     let uu____18854 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18854 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18948  ->
                                                   fun uu____18949  ->
                                                     match (uu____18948,
                                                             uu____18949)
                                                     with
                                                     | ((x,uu____18967),
                                                        (b,uu____18969)) ->
                                                         let uu____18978 =
                                                           let uu____18985 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18985) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18978)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18987 =
                                            let uu____19008 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19008) in
                                          (uu____18987, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19076 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19076 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19165) ->
                              let uu____19170 =
                                let uu____19191 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19191 in
                              (uu____19170, true)
                          | uu____19256 when Prims.op_Negation norm1 ->
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
                          | uu____19258 ->
                              let uu____19259 =
                                let uu____19260 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19261 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19260
                                  uu____19261 in
                              failwith uu____19259)
                     | uu____19286 ->
                         let uu____19287 =
                           let uu____19288 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19288.FStar_Syntax_Syntax.n in
                         (match uu____19287 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19333 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19333 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19365 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19365 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19448 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19504 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19504
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19516 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19610  ->
                            fun lb  ->
                              match uu____19610 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19705 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19705
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19708 =
                                      let uu____19723 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19723
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19708 with
                                    | (tok,decl,env2) ->
                                        let uu____19769 =
                                          let uu____19782 =
                                            let uu____19793 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19793, tok) in
                                          uu____19782 :: toks in
                                        (uu____19769, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19516 with
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
                        | uu____19976 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19984 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19984 vars)
                            else
                              (let uu____19986 =
                                 let uu____19993 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19993) in
                               FStar_SMTEncoding_Util.mkApp uu____19986) in
                      let uu____20002 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_20006  ->
                                 match uu___116_20006 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____20007 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____20013 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____20013))) in
                      if uu____20002
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____20051;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____20053;
                                FStar_Syntax_Syntax.lbeff = uu____20054;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____20117 =
                                 let uu____20124 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____20124 with
                                 | (tcenv',uu____20142,e_t) ->
                                     let uu____20148 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____20159 -> failwith "Impossible" in
                                     (match uu____20148 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_20175 = env1 in
                                            {
                                              bindings =
                                                (uu___149_20175.bindings);
                                              depth = (uu___149_20175.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_20175.warn);
                                              cache = (uu___149_20175.cache);
                                              nolabels =
                                                (uu___149_20175.nolabels);
                                              use_zfuel_name =
                                                (uu___149_20175.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_20175.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_20175.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____20117 with
                                | (env',e1,t_norm1) ->
                                    let uu____20185 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____20185 with
                                     | ((binders,body,uu____20206,uu____20207),curry)
                                         ->
                                         ((let uu____20218 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____20218
                                           then
                                             let uu____20219 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____20220 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____20219 uu____20220
                                           else ());
                                          (let uu____20222 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____20222 with
                                           | (vars,guards,env'1,binder_decls,uu____20249)
                                               ->
                                               let body1 =
                                                 let uu____20263 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____20263
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____20266 =
                                                 let uu____20275 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____20275
                                                 then
                                                   let uu____20286 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____20287 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____20286, uu____20287)
                                                 else
                                                   (let uu____20297 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____20297)) in
                                               (match uu____20266 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____20320 =
                                                        let uu____20327 =
                                                          let uu____20328 =
                                                            let uu____20339 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____20339) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____20328 in
                                                        let uu____20350 =
                                                          let uu____20353 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____20353 in
                                                        (uu____20327,
                                                          uu____20350,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____20320 in
                                                    let uu____20356 =
                                                      let uu____20359 =
                                                        let uu____20362 =
                                                          let uu____20365 =
                                                            let uu____20368 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____20368 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____20365 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____20362 in
                                                      FStar_List.append
                                                        decls1 uu____20359 in
                                                    (uu____20356, env1))))))
                           | uu____20373 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____20408 = varops.fresh "fuel" in
                             (uu____20408, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____20411 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____20499  ->
                                     fun uu____20500  ->
                                       match (uu____20499, uu____20500) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____20648 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____20648 in
                                           let gtok =
                                             let uu____20650 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____20650 in
                                           let env3 =
                                             let uu____20652 =
                                               let uu____20655 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_42  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_42) uu____20655 in
                                             push_free_var env2 flid gtok
                                               uu____20652 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____20411 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____20811
                                 t_norm uu____20813 =
                                 match (uu____20811, uu____20813) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____20857;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____20858;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____20886 =
                                       let uu____20893 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____20893 with
                                       | (tcenv',uu____20915,e_t) ->
                                           let uu____20921 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____20932 ->
                                                 failwith "Impossible" in
                                           (match uu____20921 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_20948 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_20948.bindings);
                                                    depth =
                                                      (uu___150_20948.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_20948.warn);
                                                    cache =
                                                      (uu___150_20948.cache);
                                                    nolabels =
                                                      (uu___150_20948.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_20948.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_20948.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_20948.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____20886 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____20963 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____20963
                                            then
                                              let uu____20964 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____20965 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____20966 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____20964 uu____20965
                                                uu____20966
                                            else ());
                                           (let uu____20968 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____20968 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____21005 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____21005
                                                  then
                                                    let uu____21006 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____21007 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____21008 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____21009 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____21006 uu____21007
                                                      uu____21008 uu____21009
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____21013 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____21013 with
                                                  | (vars,guards,env'1,binder_decls,uu____21044)
                                                      ->
                                                      let decl_g =
                                                        let uu____21058 =
                                                          let uu____21069 =
                                                            let uu____21072 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____21072 in
                                                          (g, uu____21069,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____21058 in
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
                                                        let uu____21097 =
                                                          let uu____21104 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____21104) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21097 in
                                                      let gsapp =
                                                        let uu____21114 =
                                                          let uu____21121 =
                                                            let uu____21124 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____21124 ::
                                                              vars_tm in
                                                          (g, uu____21121) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21114 in
                                                      let gmax =
                                                        let uu____21130 =
                                                          let uu____21137 =
                                                            let uu____21140 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____21140 ::
                                                              vars_tm in
                                                          (g, uu____21137) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21130 in
                                                      let body1 =
                                                        let uu____21146 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____21146
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____21148 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____21148 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____21166
                                                               =
                                                               let uu____21173
                                                                 =
                                                                 let uu____21174
                                                                   =
                                                                   let uu____21189
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
                                                                    uu____21189) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____21174 in
                                                               let uu____21210
                                                                 =
                                                                 let uu____21213
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____21213 in
                                                               (uu____21173,
                                                                 uu____21210,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21166 in
                                                           let eqn_f =
                                                             let uu____21217
                                                               =
                                                               let uu____21224
                                                                 =
                                                                 let uu____21225
                                                                   =
                                                                   let uu____21236
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____21236) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21225 in
                                                               (uu____21224,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21217 in
                                                           let eqn_g' =
                                                             let uu____21250
                                                               =
                                                               let uu____21257
                                                                 =
                                                                 let uu____21258
                                                                   =
                                                                   let uu____21269
                                                                    =
                                                                    let uu____21270
                                                                    =
                                                                    let uu____21275
                                                                    =
                                                                    let uu____21276
                                                                    =
                                                                    let uu____21283
                                                                    =
                                                                    let uu____21286
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21286
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21283) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21276 in
                                                                    (gsapp,
                                                                    uu____21275) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____21270 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____21269) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21258 in
                                                               (uu____21257,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21250 in
                                                           let uu____21309 =
                                                             let uu____21318
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____21318
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____21347)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____21372
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____21372
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____21377
                                                                    =
                                                                    let uu____21384
                                                                    =
                                                                    let uu____21385
                                                                    =
                                                                    let uu____21396
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21396) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21385 in
                                                                    (uu____21384,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21377 in
                                                                 let uu____21417
                                                                   =
                                                                   let uu____21424
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____21424
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____21437
                                                                    =
                                                                    let uu____21440
                                                                    =
                                                                    let uu____21441
                                                                    =
                                                                    let uu____21448
                                                                    =
                                                                    let uu____21449
                                                                    =
                                                                    let uu____21460
                                                                    =
                                                                    let uu____21461
                                                                    =
                                                                    let uu____21466
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21466,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21461 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21460) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21449 in
                                                                    (uu____21448,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21441 in
                                                                    [uu____21440] in
                                                                    (d3,
                                                                    uu____21437) in
                                                                 (match uu____21417
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____21309
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____21531 =
                                 let uu____21544 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____21623  ->
                                      fun uu____21624  ->
                                        match (uu____21623, uu____21624) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____21779 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____21779 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____21544 in
                               (match uu____21531 with
                                | (decls2,eqns,env01) ->
                                    let uu____21852 =
                                      let isDeclFun uu___117_21864 =
                                        match uu___117_21864 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____21865 -> true
                                        | uu____21876 -> false in
                                      let uu____21877 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____21877
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____21852 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____21928 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21928
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
        let uu____21977 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21977 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21981 = encode_sigelt' env se in
      match uu____21981 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21997 =
                  let uu____21998 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21998 in
                [uu____21997]
            | uu____21999 ->
                let uu____22000 =
                  let uu____22003 =
                    let uu____22004 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22004 in
                  uu____22003 :: g in
                let uu____22005 =
                  let uu____22008 =
                    let uu____22009 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22009 in
                  [uu____22008] in
                FStar_List.append uu____22000 uu____22005 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22022 =
          let uu____22023 = FStar_Syntax_Subst.compress t in
          uu____22023.FStar_Syntax_Syntax.n in
        match uu____22022 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22027)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____22032 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22037 =
          let uu____22038 = FStar_Syntax_Subst.compress t in
          uu____22038.FStar_Syntax_Syntax.n in
        match uu____22037 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22042)) ->
            (FStar_Util.string_of_bytes bytes) = "uninterpreted_by_smt"
        | uu____22047 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22052 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22057 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22060 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22063 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22078 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22082 =
            let uu____22083 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22083 Prims.op_Negation in
          if uu____22082
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22109 ->
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
               let uu____22129 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22129 with
               | (aname,atok,env2) ->
                   let uu____22145 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22145 with
                    | (formals,uu____22163) ->
                        let uu____22176 =
                          let uu____22181 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22181 env2 in
                        (match uu____22176 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22193 =
                                 let uu____22194 =
                                   let uu____22205 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22221  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22205,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22194 in
                               [uu____22193;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22234 =
                               let aux uu____22286 uu____22287 =
                                 match (uu____22286, uu____22287) with
                                 | ((bv,uu____22339),(env3,acc_sorts,acc)) ->
                                     let uu____22377 = gen_term_var env3 bv in
                                     (match uu____22377 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22234 with
                              | (uu____22449,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22472 =
                                      let uu____22479 =
                                        let uu____22480 =
                                          let uu____22491 =
                                            let uu____22492 =
                                              let uu____22497 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22497) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22492 in
                                          ([[app]], xs_sorts, uu____22491) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22480 in
                                      (uu____22479,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22472 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22517 =
                                      let uu____22524 =
                                        let uu____22525 =
                                          let uu____22536 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22536) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22525 in
                                      (uu____22524,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22517 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22555 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22555 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22583,uu____22584)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22585 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22585 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22602,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22608 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_22612  ->
                      match uu___118_22612 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22613 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22618 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22619 -> false)) in
            Prims.op_Negation uu____22608 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22628 =
               let uu____22635 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22635 env fv t quals in
             match uu____22628 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22650 =
                   let uu____22653 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22653 in
                 (uu____22650, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22661 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22661 with
           | (uu____22670,f1) ->
               let uu____22672 = encode_formula f1 env in
               (match uu____22672 with
                | (f2,decls) ->
                    let g =
                      let uu____22686 =
                        let uu____22687 =
                          let uu____22694 =
                            let uu____22697 =
                              let uu____22698 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22698 in
                            FStar_Pervasives_Native.Some uu____22697 in
                          let uu____22699 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22694, uu____22699) in
                        FStar_SMTEncoding_Util.mkAssume uu____22687 in
                      [uu____22686] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22705) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22717 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22735 =
                       let uu____22738 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22738.FStar_Syntax_Syntax.fv_name in
                     uu____22735.FStar_Syntax_Syntax.v in
                   let uu____22739 =
                     let uu____22740 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22740 in
                   if uu____22739
                   then
                     let val_decl =
                       let uu___151_22768 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_22768.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_22768.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_22768.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22773 = encode_sigelt' env1 val_decl in
                     match uu____22773 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22717 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22801,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22803;
                          FStar_Syntax_Syntax.lbtyp = uu____22804;
                          FStar_Syntax_Syntax.lbeff = uu____22805;
                          FStar_Syntax_Syntax.lbdef = uu____22806;_}::[]),uu____22807)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22826 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22826 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22855 =
                   let uu____22858 =
                     let uu____22859 =
                       let uu____22866 =
                         let uu____22867 =
                           let uu____22878 =
                             let uu____22879 =
                               let uu____22884 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22884) in
                             FStar_SMTEncoding_Util.mkEq uu____22879 in
                           ([[b2t_x]], [xx], uu____22878) in
                         FStar_SMTEncoding_Util.mkForall uu____22867 in
                       (uu____22866,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22859 in
                   [uu____22858] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22855 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22917,uu____22918) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_22927  ->
                  match uu___119_22927 with
                  | FStar_Syntax_Syntax.Discriminator uu____22928 -> true
                  | uu____22929 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22932,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22943 =
                     let uu____22944 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22944.FStar_Ident.idText in
                   uu____22943 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_22948  ->
                     match uu___120_22948 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22949 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22953) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_22970  ->
                  match uu___121_22970 with
                  | FStar_Syntax_Syntax.Projector uu____22971 -> true
                  | uu____22976 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22979 = try_lookup_free_var env l in
          (match uu____22979 with
           | FStar_Pervasives_Native.Some uu____22986 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_22990 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_22990.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_22990.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_22990.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22997) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23015) ->
          let uu____23024 = encode_sigelts env ses in
          (match uu____23024 with
           | (g,env1) ->
               let uu____23041 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_23064  ->
                         match uu___122_23064 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23065;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23066;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23067;_}
                             -> false
                         | uu____23070 -> true)) in
               (match uu____23041 with
                | (g',inversions) ->
                    let uu____23085 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_23106  ->
                              match uu___123_23106 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23107 ->
                                  true
                              | uu____23118 -> false)) in
                    (match uu____23085 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23136,tps,k,uu____23139,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_23156  ->
                    match uu___124_23156 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23157 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23166 = c in
              match uu____23166 with
              | (name,args,uu____23171,uu____23172,uu____23173) ->
                  let uu____23178 =
                    let uu____23179 =
                      let uu____23190 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23207  ->
                                match uu____23207 with
                                | (uu____23214,sort,uu____23216) -> sort)) in
                      (name, uu____23190, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23179 in
                  [uu____23178]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23243 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23249 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23249 FStar_Option.isNone)) in
            if uu____23243
            then []
            else
              (let uu____23281 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23281 with
               | (xxsym,xx) ->
                   let uu____23290 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23329  ->
                             fun l  ->
                               match uu____23329 with
                               | (out,decls) ->
                                   let uu____23349 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23349 with
                                    | (uu____23360,data_t) ->
                                        let uu____23362 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23362 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23408 =
                                                 let uu____23409 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23409.FStar_Syntax_Syntax.n in
                                               match uu____23408 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23420,indices) ->
                                                   indices
                                               | uu____23442 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23466  ->
                                                         match uu____23466
                                                         with
                                                         | (x,uu____23472) ->
                                                             let uu____23473
                                                               =
                                                               let uu____23474
                                                                 =
                                                                 let uu____23481
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23481,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23474 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23473)
                                                    env) in
                                             let uu____23484 =
                                               encode_args indices env1 in
                                             (match uu____23484 with
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
                                                      let uu____23510 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23526
                                                                 =
                                                                 let uu____23531
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23531,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23526)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23510
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23534 =
                                                      let uu____23535 =
                                                        let uu____23540 =
                                                          let uu____23541 =
                                                            let uu____23546 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23546,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23541 in
                                                        (out, uu____23540) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23535 in
                                                    (uu____23534,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23290 with
                    | (data_ax,decls) ->
                        let uu____23559 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23559 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23570 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23570 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23574 =
                                 let uu____23581 =
                                   let uu____23582 =
                                     let uu____23593 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23608 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23593,
                                       uu____23608) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23582 in
                                 let uu____23623 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23581,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23623) in
                               FStar_SMTEncoding_Util.mkAssume uu____23574 in
                             let pattern_guarded_inversion =
                               let uu____23629 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____23629
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____23636 =
                                   let uu____23637 =
                                     let uu____23644 =
                                       let uu____23645 =
                                         let uu____23656 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____23671 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____23656, uu____23671) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____23645 in
                                     let uu____23686 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____23644,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____23686) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____23637 in
                                 [uu____23636]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____23690 =
            let uu____23703 =
              let uu____23704 = FStar_Syntax_Subst.compress k in
              uu____23704.FStar_Syntax_Syntax.n in
            match uu____23703 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23749 -> (tps, k) in
          (match uu____23690 with
           | (formals,res) ->
               let uu____23772 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23772 with
                | (formals1,res1) ->
                    let uu____23783 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23783 with
                     | (vars,guards,env',binder_decls,uu____23808) ->
                         let uu____23821 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23821 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23840 =
                                  let uu____23847 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23847) in
                                FStar_SMTEncoding_Util.mkApp uu____23840 in
                              let uu____23856 =
                                let tname_decl =
                                  let uu____23866 =
                                    let uu____23867 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23899  ->
                                              match uu____23899 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23912 = varops.next_id () in
                                    (tname, uu____23867,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23912, false) in
                                  constructor_or_logic_type_decl uu____23866 in
                                let uu____23921 =
                                  match vars with
                                  | [] ->
                                      let uu____23934 =
                                        let uu____23935 =
                                          let uu____23938 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____23938 in
                                        push_free_var env1 t tname
                                          uu____23935 in
                                      ([], uu____23934)
                                  | uu____23945 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23954 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23954 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23968 =
                                          let uu____23975 =
                                            let uu____23976 =
                                              let uu____23991 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23991) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23976 in
                                          (uu____23975,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23968 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23921 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23856 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24031 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24031 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24049 =
                                               let uu____24050 =
                                                 let uu____24057 =
                                                   let uu____24058 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24058 in
                                                 (uu____24057,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24050 in
                                             [uu____24049]
                                           else [] in
                                         let uu____24062 =
                                           let uu____24065 =
                                             let uu____24068 =
                                               let uu____24069 =
                                                 let uu____24076 =
                                                   let uu____24077 =
                                                     let uu____24088 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24088) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24077 in
                                                 (uu____24076,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24069 in
                                             [uu____24068] in
                                           FStar_List.append karr uu____24065 in
                                         FStar_List.append decls1 uu____24062 in
                                   let aux =
                                     let uu____24104 =
                                       let uu____24107 =
                                         inversion_axioms tapp vars in
                                       let uu____24110 =
                                         let uu____24113 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24113] in
                                       FStar_List.append uu____24107
                                         uu____24110 in
                                     FStar_List.append kindingAx uu____24104 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24120,uu____24121,uu____24122,uu____24123,uu____24124)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24132,t,uu____24134,n_tps,uu____24136) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24144 = new_term_constant_and_tok_from_lid env d in
          (match uu____24144 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24161 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24161 with
                | (formals,t_res) ->
                    let uu____24196 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24196 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24210 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24210 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24280 =
                                            mk_term_projector_name d x in
                                          (uu____24280,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24282 =
                                  let uu____24301 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24301, true) in
                                FStar_All.pipe_right uu____24282
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
                              let uu____24340 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24340 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24352::uu____24353 ->
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
                                         let uu____24398 =
                                           let uu____24409 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24409) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24398
                                     | uu____24434 -> tok_typing in
                                   let uu____24443 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24443 with
                                    | (vars',guards',env'',decls_formals,uu____24468)
                                        ->
                                        let uu____24481 =
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
                                        (match uu____24481 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24512 ->
                                                   let uu____24519 =
                                                     let uu____24520 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24520 in
                                                   [uu____24519] in
                                             let encode_elim uu____24530 =
                                               let uu____24531 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24531 with
                                               | (head1,args) ->
                                                   let uu____24574 =
                                                     let uu____24575 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24575.FStar_Syntax_Syntax.n in
                                                   (match uu____24574 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24585;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24586;_},uu____24587)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24593 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24593
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
                                                                 | uu____24636
                                                                    ->
                                                                    let uu____24637
                                                                    =
                                                                    let uu____24638
                                                                    =
                                                                    let uu____24643
                                                                    =
                                                                    let uu____24644
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24644 in
                                                                    (uu____24643,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24638 in
                                                                    FStar_Exn.raise
                                                                    uu____24637 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24660
                                                                    =
                                                                    let uu____24661
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24661 in
                                                                    if
                                                                    uu____24660
                                                                    then
                                                                    let uu____24674
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24674]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24676
                                                               =
                                                               let uu____24689
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24739
                                                                     ->
                                                                    fun
                                                                    uu____24740
                                                                     ->
                                                                    match 
                                                                    (uu____24739,
                                                                    uu____24740)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24835
                                                                    =
                                                                    let uu____24842
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24842 in
                                                                    (match uu____24835
                                                                    with
                                                                    | 
                                                                    (uu____24855,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24863
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24863
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24865
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24865
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
                                                                 uu____24689 in
                                                             (match uu____24676
                                                              with
                                                              | (uu____24880,arg_vars,elim_eqns_or_guards,uu____24883)
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
                                                                    let uu____24913
                                                                    =
                                                                    let uu____24920
                                                                    =
                                                                    let uu____24921
                                                                    =
                                                                    let uu____24932
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24943
                                                                    =
                                                                    let uu____24944
                                                                    =
                                                                    let uu____24949
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24949) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24944 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24932,
                                                                    uu____24943) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24921 in
                                                                    (uu____24920,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24913 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24972
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24972,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24974
                                                                    =
                                                                    let uu____24981
                                                                    =
                                                                    let uu____24982
                                                                    =
                                                                    let uu____24993
                                                                    =
                                                                    let uu____24998
                                                                    =
                                                                    let uu____25001
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25001] in
                                                                    [uu____24998] in
                                                                    let uu____25006
                                                                    =
                                                                    let uu____25007
                                                                    =
                                                                    let uu____25012
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25013
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25012,
                                                                    uu____25013) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25007 in
                                                                    (uu____24993,
                                                                    [x],
                                                                    uu____25006) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24982 in
                                                                    let uu____25032
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24981,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25032) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24974
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25039
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
                                                                    (let uu____25067
                                                                    =
                                                                    let uu____25068
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25068
                                                                    dapp1 in
                                                                    [uu____25067]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25039
                                                                    FStar_List.flatten in
                                                                    let uu____25075
                                                                    =
                                                                    let uu____25082
                                                                    =
                                                                    let uu____25083
                                                                    =
                                                                    let uu____25094
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25105
                                                                    =
                                                                    let uu____25106
                                                                    =
                                                                    let uu____25111
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25111) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25106 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25094,
                                                                    uu____25105) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25083 in
                                                                    (uu____25082,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25075) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25132 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25132
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
                                                                 | uu____25175
                                                                    ->
                                                                    let uu____25176
                                                                    =
                                                                    let uu____25177
                                                                    =
                                                                    let uu____25182
                                                                    =
                                                                    let uu____25183
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25183 in
                                                                    (uu____25182,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25177 in
                                                                    FStar_Exn.raise
                                                                    uu____25176 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25199
                                                                    =
                                                                    let uu____25200
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25200 in
                                                                    if
                                                                    uu____25199
                                                                    then
                                                                    let uu____25213
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25213]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25215
                                                               =
                                                               let uu____25228
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25278
                                                                     ->
                                                                    fun
                                                                    uu____25279
                                                                     ->
                                                                    match 
                                                                    (uu____25278,
                                                                    uu____25279)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25374
                                                                    =
                                                                    let uu____25381
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25381 in
                                                                    (match uu____25374
                                                                    with
                                                                    | 
                                                                    (uu____25394,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25402
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25402
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25404
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25404
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
                                                                 uu____25228 in
                                                             (match uu____25215
                                                              with
                                                              | (uu____25419,arg_vars,elim_eqns_or_guards,uu____25422)
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
                                                                    let uu____25452
                                                                    =
                                                                    let uu____25459
                                                                    =
                                                                    let uu____25460
                                                                    =
                                                                    let uu____25471
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25483
                                                                    =
                                                                    let uu____25488
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25488) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25483 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25471,
                                                                    uu____25482) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25460 in
                                                                    (uu____25459,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25452 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25511
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25511,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25513
                                                                    =
                                                                    let uu____25520
                                                                    =
                                                                    let uu____25521
                                                                    =
                                                                    let uu____25532
                                                                    =
                                                                    let uu____25537
                                                                    =
                                                                    let uu____25540
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25540] in
                                                                    [uu____25537] in
                                                                    let uu____25545
                                                                    =
                                                                    let uu____25546
                                                                    =
                                                                    let uu____25551
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25552
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25551,
                                                                    uu____25552) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25546 in
                                                                    (uu____25532,
                                                                    [x],
                                                                    uu____25545) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25521 in
                                                                    let uu____25571
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25520,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25571) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25513
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25578
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
                                                                    (let uu____25606
                                                                    =
                                                                    let uu____25607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25607
                                                                    dapp1 in
                                                                    [uu____25606]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25578
                                                                    FStar_List.flatten in
                                                                    let uu____25614
                                                                    =
                                                                    let uu____25621
                                                                    =
                                                                    let uu____25622
                                                                    =
                                                                    let uu____25633
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25644
                                                                    =
                                                                    let uu____25645
                                                                    =
                                                                    let uu____25650
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25650) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25645 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25633,
                                                                    uu____25644) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25622 in
                                                                    (uu____25621,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25614) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25669 ->
                                                        ((let uu____25671 =
                                                            let uu____25672 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25673 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25672
                                                              uu____25673 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25671);
                                                         ([], []))) in
                                             let uu____25678 = encode_elim () in
                                             (match uu____25678 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25698 =
                                                      let uu____25701 =
                                                        let uu____25704 =
                                                          let uu____25707 =
                                                            let uu____25710 =
                                                              let uu____25711
                                                                =
                                                                let uu____25722
                                                                  =
                                                                  let uu____25725
                                                                    =
                                                                    let uu____25726
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25726 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25725 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25722) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25711 in
                                                            [uu____25710] in
                                                          let uu____25731 =
                                                            let uu____25734 =
                                                              let uu____25737
                                                                =
                                                                let uu____25740
                                                                  =
                                                                  let uu____25743
                                                                    =
                                                                    let uu____25746
                                                                    =
                                                                    let uu____25749
                                                                    =
                                                                    let uu____25750
                                                                    =
                                                                    let uu____25757
                                                                    =
                                                                    let uu____25758
                                                                    =
                                                                    let uu____25769
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25769) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25758 in
                                                                    (uu____25757,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25750 in
                                                                    let uu____25782
                                                                    =
                                                                    let uu____25785
                                                                    =
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
                                                                    vars' in
                                                                    let uu____25816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25805,
                                                                    uu____25816) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25794 in
                                                                    (uu____25793,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25786 in
                                                                    [uu____25785] in
                                                                    uu____25749
                                                                    ::
                                                                    uu____25782 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25746 in
                                                                  FStar_List.append
                                                                    uu____25743
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25740 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25737 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25734 in
                                                          FStar_List.append
                                                            uu____25707
                                                            uu____25731 in
                                                        FStar_List.append
                                                          decls3 uu____25704 in
                                                      FStar_List.append
                                                        decls2 uu____25701 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25698 in
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
           (fun uu____25862  ->
              fun se  ->
                match uu____25862 with
                | (g,env1) ->
                    let uu____25882 = encode_sigelt env1 se in
                    (match uu____25882 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25941 =
        match uu____25941 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25973 ->
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
                 ((let uu____25979 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25979
                   then
                     let uu____25980 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25981 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25982 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25980 uu____25981 uu____25982
                   else ());
                  (let uu____25984 = encode_term t1 env1 in
                   match uu____25984 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26000 =
                         let uu____26007 =
                           let uu____26008 =
                             let uu____26009 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26009
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26008 in
                         new_term_constant_from_string env1 x uu____26007 in
                       (match uu____26000 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26025 = FStar_Options.log_queries () in
                              if uu____26025
                              then
                                let uu____26028 =
                                  let uu____26029 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26030 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26031 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26029 uu____26030 uu____26031 in
                                FStar_Pervasives_Native.Some uu____26028
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26047,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26061 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26061 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26084,se,uu____26086) ->
                 let uu____26091 = encode_sigelt env1 se in
                 (match uu____26091 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26108,se) ->
                 let uu____26114 = encode_sigelt env1 se in
                 (match uu____26114 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26131 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26131 with | (uu____26154,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26169 'Auu____26170 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26170,'Auu____26169)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26238  ->
              match uu____26238 with
              | (l,uu____26250,uu____26251) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26297  ->
              match uu____26297 with
              | (l,uu____26311,uu____26312) ->
                  let uu____26321 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26322 =
                    let uu____26325 =
                      let uu____26326 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26326 in
                    [uu____26325] in
                  uu____26321 :: uu____26322)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26348 =
      let uu____26351 =
        let uu____26352 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26355 =
          let uu____26356 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26356 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26352;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26355
        } in
      [uu____26351] in
    FStar_ST.op_Colon_Equals last_env uu____26348
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26383 = FStar_ST.op_Bang last_env in
      match uu____26383 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26405 ->
          let uu___153_26408 = e in
          let uu____26409 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_26408.bindings);
            depth = (uu___153_26408.depth);
            tcenv;
            warn = (uu___153_26408.warn);
            cache = (uu___153_26408.cache);
            nolabels = (uu___153_26408.nolabels);
            use_zfuel_name = (uu___153_26408.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_26408.encode_non_total_function_typ);
            current_module_name = uu____26409
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26414 = FStar_ST.op_Bang last_env in
    match uu____26414 with
    | [] -> failwith "Empty env stack"
    | uu____26435::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26460  ->
    let uu____26461 = FStar_ST.op_Bang last_env in
    match uu____26461 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_26490 = hd1 in
          {
            bindings = (uu___154_26490.bindings);
            depth = (uu___154_26490.depth);
            tcenv = (uu___154_26490.tcenv);
            warn = (uu___154_26490.warn);
            cache = refs;
            nolabels = (uu___154_26490.nolabels);
            use_zfuel_name = (uu___154_26490.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_26490.encode_non_total_function_typ);
            current_module_name = (uu___154_26490.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26512  ->
    let uu____26513 = FStar_ST.op_Bang last_env in
    match uu____26513 with
    | [] -> failwith "Popping an empty stack"
    | uu____26534::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____26559  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____26563  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____26567  ->
    let uu____26568 = FStar_ST.op_Bang last_env in
    match uu____26568 with
    | hd1::uu____26590::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26612 -> failwith "Impossible"
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
        | (uu____26677::uu____26678,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_26686 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_26686.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_26686.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_26686.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26687 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26704 =
        let uu____26707 =
          let uu____26708 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26708 in
        let uu____26709 = open_fact_db_tags env in uu____26707 :: uu____26709 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26704
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
      let uu____26733 = encode_sigelt env se in
      match uu____26733 with
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
        let uu____26771 = FStar_Options.log_queries () in
        if uu____26771
        then
          let uu____26774 =
            let uu____26775 =
              let uu____26776 =
                let uu____26777 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26777 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26776 in
            FStar_SMTEncoding_Term.Caption uu____26775 in
          uu____26774 :: decls
        else decls in
      let env =
        let uu____26788 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26788 tcenv in
      let uu____26789 = encode_top_level_facts env se in
      match uu____26789 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26803 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26803))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26817 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26817
       then
         let uu____26818 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26818
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26853  ->
                 fun se  ->
                   match uu____26853 with
                   | (g,env2) ->
                       let uu____26873 = encode_top_level_facts env2 se in
                       (match uu____26873 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26896 =
         encode_signature
           (let uu___156_26905 = env in
            {
              bindings = (uu___156_26905.bindings);
              depth = (uu___156_26905.depth);
              tcenv = (uu___156_26905.tcenv);
              warn = false;
              cache = (uu___156_26905.cache);
              nolabels = (uu___156_26905.nolabels);
              use_zfuel_name = (uu___156_26905.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_26905.encode_non_total_function_typ);
              current_module_name = (uu___156_26905.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26896 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26922 = FStar_Options.log_queries () in
             if uu____26922
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_26930 = env1 in
               {
                 bindings = (uu___157_26930.bindings);
                 depth = (uu___157_26930.depth);
                 tcenv = (uu___157_26930.tcenv);
                 warn = true;
                 cache = (uu___157_26930.cache);
                 nolabels = (uu___157_26930.nolabels);
                 use_zfuel_name = (uu___157_26930.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_26930.encode_non_total_function_typ);
                 current_module_name = (uu___157_26930.current_module_name)
               });
            (let uu____26932 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26932
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
        (let uu____26987 =
           let uu____26988 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26988.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26987);
        (let env =
           let uu____26990 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26990 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27002 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27037 = aux rest in
                 (match uu____27037 with
                  | (out,rest1) ->
                      let t =
                        let uu____27067 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27067 with
                        | FStar_Pervasives_Native.Some uu____27072 ->
                            let uu____27073 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27073
                              x.FStar_Syntax_Syntax.sort
                        | uu____27074 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27078 =
                        let uu____27081 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_27084 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_27084.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_27084.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27081 :: out in
                      (uu____27078, rest1))
             | uu____27089 -> ([], bindings1) in
           let uu____27096 = aux bindings in
           match uu____27096 with
           | (closing,bindings1) ->
               let uu____27121 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27121, bindings1) in
         match uu____27002 with
         | (q1,bindings1) ->
             let uu____27144 =
               let uu____27149 =
                 FStar_List.filter
                   (fun uu___125_27154  ->
                      match uu___125_27154 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27155 ->
                          false
                      | uu____27162 -> true) bindings1 in
               encode_env_bindings env uu____27149 in
             (match uu____27144 with
              | (env_decls,env1) ->
                  ((let uu____27180 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27180
                    then
                      let uu____27181 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27181
                    else ());
                   (let uu____27183 = encode_formula q1 env1 in
                    match uu____27183 with
                    | (phi,qdecls) ->
                        let uu____27204 =
                          let uu____27209 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27209 phi in
                        (match uu____27204 with
                         | (labels,phi1) ->
                             let uu____27226 = encode_labels labels in
                             (match uu____27226 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27263 =
                                      let uu____27270 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27271 =
                                        varops.mk_unique "@query" in
                                      (uu____27270,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27271) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27263 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____27290 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27290 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27292 = encode_formula q env in
       match uu____27292 with
       | (f,uu____27298) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27300) -> true
             | uu____27305 -> false)))