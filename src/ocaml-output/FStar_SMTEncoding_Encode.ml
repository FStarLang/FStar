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
      (fun uu___106_119  ->
         match uu___106_119 with
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
        let uu___130_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___130_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___130_221.FStar_Syntax_Syntax.sort)
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
    let uu___131_2159 = x in
    let uu____2160 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____2160;
      FStar_Syntax_Syntax.index = (uu___131_2159.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___131_2159.FStar_Syntax_Syntax.sort)
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
                 (fun uu___107_2632  ->
                    match uu___107_2632 with
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
           (fun uu___108_2657  ->
              match uu___108_2657 with
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
        (let uu___132_2746 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___132_2746.tcenv);
           warn = (uu___132_2746.warn);
           cache = (uu___132_2746.cache);
           nolabels = (uu___132_2746.nolabels);
           use_zfuel_name = (uu___132_2746.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___132_2746.encode_non_total_function_typ);
           current_module_name = (uu___132_2746.current_module_name)
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
        (let uu___133_2766 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___133_2766.depth);
           tcenv = (uu___133_2766.tcenv);
           warn = (uu___133_2766.warn);
           cache = (uu___133_2766.cache);
           nolabels = (uu___133_2766.nolabels);
           use_zfuel_name = (uu___133_2766.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___133_2766.encode_non_total_function_typ);
           current_module_name = (uu___133_2766.current_module_name)
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
          (let uu___134_2790 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___134_2790.depth);
             tcenv = (uu___134_2790.tcenv);
             warn = (uu___134_2790.warn);
             cache = (uu___134_2790.cache);
             nolabels = (uu___134_2790.nolabels);
             use_zfuel_name = (uu___134_2790.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___134_2790.encode_non_total_function_typ);
             current_module_name = (uu___134_2790.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___135_2803 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___135_2803.depth);
          tcenv = (uu___135_2803.tcenv);
          warn = (uu___135_2803.warn);
          cache = (uu___135_2803.cache);
          nolabels = (uu___135_2803.nolabels);
          use_zfuel_name = (uu___135_2803.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___135_2803.encode_non_total_function_typ);
          current_module_name = (uu___135_2803.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___109_2829  ->
             match uu___109_2829 with
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
        let uu___136_2902 = env in
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
          depth = (uu___136_2902.depth);
          tcenv = (uu___136_2902.tcenv);
          warn = (uu___136_2902.warn);
          cache = (uu___136_2902.cache);
          nolabels = (uu___136_2902.nolabels);
          use_zfuel_name = (uu___136_2902.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___136_2902.encode_non_total_function_typ);
          current_module_name = (uu___136_2902.current_module_name)
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
        (fun uu___110_2967  ->
           match uu___110_2967 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____3006 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____3025 =
        lookup_binding env
          (fun uu___111_3033  ->
             match uu___111_3033 with
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
          let uu___137_3155 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___137_3155.depth);
            tcenv = (uu___137_3155.tcenv);
            warn = (uu___137_3155.warn);
            cache = (uu___137_3155.cache);
            nolabels = (uu___137_3155.nolabels);
            use_zfuel_name = (uu___137_3155.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___137_3155.encode_non_total_function_typ);
            current_module_name = (uu___137_3155.current_module_name)
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
            let uu___138_3210 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___138_3210.depth);
              tcenv = (uu___138_3210.tcenv);
              warn = (uu___138_3210.warn);
              cache = (uu___138_3210.cache);
              nolabels = (uu___138_3210.nolabels);
              use_zfuel_name = (uu___138_3210.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___138_3210.encode_non_total_function_typ);
              current_module_name = (uu___138_3210.current_module_name)
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
        (fun uu___112_3464  ->
           match uu___112_3464 with
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
               (fun uu___113_3791  ->
                  match uu___113_3791 with
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
  fun uu___114_3899  ->
    match uu___114_3899 with
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
  fun uu___115_4233  ->
    match uu___115_4233 with
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
                           (let uu___139_6516 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___139_6516.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___139_6516.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___139_6516.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___139_6516.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___139_6516.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___139_6516.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___139_6516.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___139_6516.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___139_6516.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___139_6516.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___139_6516.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___139_6516.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___139_6516.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___139_6516.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___139_6516.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___139_6516.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___139_6516.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___139_6516.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___139_6516.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___139_6516.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___139_6516.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___139_6516.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___139_6516.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___139_6516.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___139_6516.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___139_6516.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___139_6516.FStar_TypeChecker_Env.identifier_info)
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
                              let uu____8606 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8606
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8608 = encode_term body2 envbody in
                            (match uu____8608 with
                             | (body3,decls') ->
                                 let uu____8619 =
                                   let uu____8628 = codomain_eff rc in
                                   match uu____8628 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8647 = encode_term tfun env in
                                       (match uu____8647 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8619 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8679 =
                                          let uu____8690 =
                                            let uu____8691 =
                                              let uu____8696 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8696, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8691 in
                                          ([], vars, uu____8690) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8679 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8708 =
                                              let uu____8711 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8711
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8708 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8730 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8730 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8738 =
                                             let uu____8739 =
                                               let uu____8746 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8746) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8739 in
                                           (uu____8738,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8757 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8757 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8768 =
                                                    let uu____8769 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8769 = cache_size in
                                                  if uu____8768
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
                                                    let uu____8785 =
                                                      let uu____8786 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8786 in
                                                    varops.mk_unique
                                                      uu____8785 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8793 =
                                                    let uu____8800 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8800) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8793 in
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
                                                      let uu____8818 =
                                                        let uu____8819 =
                                                          let uu____8826 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8826,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8819 in
                                                      [uu____8818] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8839 =
                                                    let uu____8846 =
                                                      let uu____8847 =
                                                        let uu____8858 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8858) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8847 in
                                                    (uu____8846,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8839 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8875 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8875);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8878,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8879;
                          FStar_Syntax_Syntax.lbunivs = uu____8880;
                          FStar_Syntax_Syntax.lbtyp = uu____8881;
                          FStar_Syntax_Syntax.lbeff = uu____8882;
                          FStar_Syntax_Syntax.lbdef = uu____8883;_}::uu____8884),uu____8885)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8911;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8913;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8934 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____8954 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____8954, [decl_e])))
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
              let uu____9009 = encode_term e1 env in
              match uu____9009 with
              | (ee1,decls1) ->
                  let uu____9020 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____9020 with
                   | (xs,e21) ->
                       let uu____9045 = FStar_List.hd xs in
                       (match uu____9045 with
                        | (x1,uu____9059) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____9061 = encode_body e21 env' in
                            (match uu____9061 with
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
            let uu____9093 =
              let uu____9100 =
                let uu____9101 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____9101 in
              gen_term_var env uu____9100 in
            match uu____9093 with
            | (scrsym,scr',env1) ->
                let uu____9109 = encode_term e env1 in
                (match uu____9109 with
                 | (scr,decls) ->
                     let uu____9120 =
                       let encode_branch b uu____9145 =
                         match uu____9145 with
                         | (else_case,decls1) ->
                             let uu____9164 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9164 with
                              | (p,w,br) ->
                                  let uu____9190 = encode_pat env1 p in
                                  (match uu____9190 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9227  ->
                                                   match uu____9227 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9234 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9256 =
                                               encode_term w1 env2 in
                                             (match uu____9256 with
                                              | (w2,decls2) ->
                                                  let uu____9269 =
                                                    let uu____9270 =
                                                      let uu____9275 =
                                                        let uu____9276 =
                                                          let uu____9281 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9281) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9276 in
                                                      (guard, uu____9275) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9270 in
                                                  (uu____9269, decls2)) in
                                       (match uu____9234 with
                                        | (guard1,decls2) ->
                                            let uu____9294 =
                                              encode_br br env2 in
                                            (match uu____9294 with
                                             | (br1,decls3) ->
                                                 let uu____9307 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9307,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____9120 with
                      | (match_tm,decls1) ->
                          let uu____9326 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9326, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9366 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9366
       then
         let uu____9367 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9367
       else ());
      (let uu____9369 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9369 with
       | (vars,pat_term) ->
           let uu____9386 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9439  ->
                     fun v1  ->
                       match uu____9439 with
                       | (env1,vars1) ->
                           let uu____9491 = gen_term_var env1 v1 in
                           (match uu____9491 with
                            | (xx,uu____9513,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9386 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9592 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9593 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9594 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9602 =
                        let uu____9607 = encode_const c in
                        (scrutinee, uu____9607) in
                      FStar_SMTEncoding_Util.mkEq uu____9602
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9628 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9628 with
                        | (uu____9635,uu____9636::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9639 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9672  ->
                                  match uu____9672 with
                                  | (arg,uu____9680) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9686 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9686)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9713) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9744 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9767 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9811  ->
                                  match uu____9811 with
                                  | (arg,uu____9825) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9831 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9831)) in
                      FStar_All.pipe_right uu____9767 FStar_List.flatten in
                let pat_term1 uu____9859 = encode_term pat_term env1 in
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
      let uu____9869 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9907  ->
                fun uu____9908  ->
                  match (uu____9907, uu____9908) with
                  | ((tms,decls),(t,uu____9944)) ->
                      let uu____9965 = encode_term t env in
                      (match uu____9965 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9869 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10022 = FStar_Syntax_Util.list_elements e in
        match uu____10022 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____10043 =
          let uu____10058 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____10058 FStar_Syntax_Util.head_and_args in
        match uu____10043 with
        | (head1,args) ->
            let uu____10097 =
              let uu____10110 =
                let uu____10111 = FStar_Syntax_Util.un_uinst head1 in
                uu____10111.FStar_Syntax_Syntax.n in
              (uu____10110, args) in
            (match uu____10097 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10125,uu____10126)::(e,uu____10128)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10163 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10199 =
            let uu____10214 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10214 FStar_Syntax_Util.head_and_args in
          match uu____10199 with
          | (head1,args) ->
              let uu____10255 =
                let uu____10268 =
                  let uu____10269 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10269.FStar_Syntax_Syntax.n in
                (uu____10268, args) in
              (match uu____10255 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10286)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10313 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10335 = smt_pat_or1 t1 in
            (match uu____10335 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10351 = list_elements1 e in
                 FStar_All.pipe_right uu____10351
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10369 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10369
                           (FStar_List.map one_pat)))
             | uu____10380 ->
                 let uu____10385 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10385])
        | uu____10406 ->
            let uu____10409 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10409] in
      let uu____10430 =
        let uu____10449 =
          let uu____10450 = FStar_Syntax_Subst.compress t in
          uu____10450.FStar_Syntax_Syntax.n in
        match uu____10449 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10489 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10489 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10532;
                        FStar_Syntax_Syntax.effect_name = uu____10533;
                        FStar_Syntax_Syntax.result_typ = uu____10534;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10536)::(post,uu____10538)::(pats,uu____10540)::[];
                        FStar_Syntax_Syntax.flags = uu____10541;_}
                      ->
                      let uu____10582 = lemma_pats pats in
                      (binders1, pre, post, uu____10582)
                  | uu____10599 -> failwith "impos"))
        | uu____10618 -> failwith "Impos" in
      match uu____10430 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___140_10666 = env in
            {
              bindings = (uu___140_10666.bindings);
              depth = (uu___140_10666.depth);
              tcenv = (uu___140_10666.tcenv);
              warn = (uu___140_10666.warn);
              cache = (uu___140_10666.cache);
              nolabels = (uu___140_10666.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___140_10666.encode_non_total_function_typ);
              current_module_name = (uu___140_10666.current_module_name)
            } in
          let uu____10667 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10667 with
           | (vars,guards,env2,decls,uu____10692) ->
               let uu____10705 =
                 let uu____10718 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10762 =
                             let uu____10771 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10771
                               FStar_List.unzip in
                           match uu____10762 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10718 FStar_List.unzip in
               (match uu____10705 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___141_10880 = env2 in
                      {
                        bindings = (uu___141_10880.bindings);
                        depth = (uu___141_10880.depth);
                        tcenv = (uu___141_10880.tcenv);
                        warn = (uu___141_10880.warn);
                        cache = (uu___141_10880.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___141_10880.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___141_10880.encode_non_total_function_typ);
                        current_module_name =
                          (uu___141_10880.current_module_name)
                      } in
                    let uu____10881 =
                      let uu____10886 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10886 env3 in
                    (match uu____10881 with
                     | (pre1,decls'') ->
                         let uu____10893 =
                           let uu____10898 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10898 env3 in
                         (match uu____10893 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10908 =
                                let uu____10909 =
                                  let uu____10920 =
                                    let uu____10921 =
                                      let uu____10926 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10926, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10921 in
                                  (pats, vars, uu____10920) in
                                FStar_SMTEncoding_Util.mkForall uu____10909 in
                              (uu____10908, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10945 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10945
        then
          let uu____10946 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10947 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10946 uu____10947
        else () in
      let enc f r l =
        let uu____10980 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11008 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11008 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10980 with
        | (decls,args) ->
            let uu____11037 =
              let uu___142_11038 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___142_11038.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___142_11038.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11037, decls) in
      let const_op f r uu____11069 =
        let uu____11082 = f r in (uu____11082, []) in
      let un_op f l =
        let uu____11101 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11101 in
      let bin_op f uu___116_11117 =
        match uu___116_11117 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11128 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11162 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11185  ->
                 match uu____11185 with
                 | (t,uu____11199) ->
                     let uu____11200 = encode_formula t env in
                     (match uu____11200 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11162 with
        | (decls,phis) ->
            let uu____11229 =
              let uu___143_11230 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_11230.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_11230.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11229, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11291  ->
               match uu____11291 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11310) -> false
                    | uu____11311 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11326 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11326
        else
          (let uu____11340 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11340 r rf) in
      let mk_imp1 r uu___117_11365 =
        match uu___117_11365 with
        | (lhs,uu____11371)::(rhs,uu____11373)::[] ->
            let uu____11400 = encode_formula rhs env in
            (match uu____11400 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11415) ->
                      (l1, decls1)
                  | uu____11420 ->
                      let uu____11421 = encode_formula lhs env in
                      (match uu____11421 with
                       | (l2,decls2) ->
                           let uu____11432 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11432, (FStar_List.append decls1 decls2)))))
        | uu____11435 -> failwith "impossible" in
      let mk_ite r uu___118_11456 =
        match uu___118_11456 with
        | (guard,uu____11462)::(_then,uu____11464)::(_else,uu____11466)::[]
            ->
            let uu____11503 = encode_formula guard env in
            (match uu____11503 with
             | (g,decls1) ->
                 let uu____11514 = encode_formula _then env in
                 (match uu____11514 with
                  | (t,decls2) ->
                      let uu____11525 = encode_formula _else env in
                      (match uu____11525 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11539 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11564 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11564 in
      let connectives =
        let uu____11582 =
          let uu____11595 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11595) in
        let uu____11612 =
          let uu____11627 =
            let uu____11640 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11640) in
          let uu____11657 =
            let uu____11672 =
              let uu____11687 =
                let uu____11700 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11700) in
              let uu____11717 =
                let uu____11732 =
                  let uu____11747 =
                    let uu____11760 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11760) in
                  [uu____11747;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11732 in
              uu____11687 :: uu____11717 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11672 in
          uu____11627 :: uu____11657 in
        uu____11582 :: uu____11612 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12081 = encode_formula phi' env in
            (match uu____12081 with
             | (phi2,decls) ->
                 let uu____12092 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12092, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12093 ->
            let uu____12100 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12100 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12139 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12139 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12151;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12153;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12174 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12174 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12221::(x,uu____12223)::(t,uu____12225)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12272 = encode_term x env in
                 (match uu____12272 with
                  | (x1,decls) ->
                      let uu____12283 = encode_term t env in
                      (match uu____12283 with
                       | (t1,decls') ->
                           let uu____12294 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12294, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12299)::(msg,uu____12301)::(phi2,uu____12303)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12348 =
                   let uu____12353 =
                     let uu____12354 = FStar_Syntax_Subst.compress r in
                     uu____12354.FStar_Syntax_Syntax.n in
                   let uu____12357 =
                     let uu____12358 = FStar_Syntax_Subst.compress msg in
                     uu____12358.FStar_Syntax_Syntax.n in
                   (uu____12353, uu____12357) in
                 (match uu____12348 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12367))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12377 -> fallback phi2)
             | uu____12382 when head_redex env head2 ->
                 let uu____12395 = whnf env phi1 in
                 encode_formula uu____12395 env
             | uu____12396 ->
                 let uu____12409 = encode_term phi1 env in
                 (match uu____12409 with
                  | (tt,decls) ->
                      let uu____12420 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___144_12423 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___144_12423.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___144_12423.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12420, decls)))
        | uu____12424 ->
            let uu____12425 = encode_term phi1 env in
            (match uu____12425 with
             | (tt,decls) ->
                 let uu____12436 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___145_12439 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___145_12439.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___145_12439.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12436, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12475 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12475 with
        | (vars,guards,env2,decls,uu____12514) ->
            let uu____12527 =
              let uu____12540 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12588 =
                          let uu____12597 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12627  ->
                                    match uu____12627 with
                                    | (t,uu____12637) ->
                                        encode_term t
                                          (let uu___146_12639 = env2 in
                                           {
                                             bindings =
                                               (uu___146_12639.bindings);
                                             depth = (uu___146_12639.depth);
                                             tcenv = (uu___146_12639.tcenv);
                                             warn = (uu___146_12639.warn);
                                             cache = (uu___146_12639.cache);
                                             nolabels =
                                               (uu___146_12639.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___146_12639.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___146_12639.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12597 FStar_List.unzip in
                        match uu____12588 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12540 FStar_List.unzip in
            (match uu____12527 with
             | (pats,decls') ->
                 let uu____12738 = encode_formula body env2 in
                 (match uu____12738 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12770;
                             FStar_SMTEncoding_Term.rng = uu____12771;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12786 -> guards in
                      let uu____12791 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12791, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12851  ->
                   match uu____12851 with
                   | (x,uu____12857) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12865 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12877 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12877) uu____12865 tl1 in
             let uu____12880 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12907  ->
                       match uu____12907 with
                       | (b,uu____12913) ->
                           let uu____12914 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12914)) in
             (match uu____12880 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12920) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12934 =
                    let uu____12935 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12935 in
                  FStar_Errors.warn pos uu____12934) in
       let uu____12936 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12936 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12945 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13003  ->
                     match uu____13003 with
                     | (l,uu____13017) -> FStar_Ident.lid_equals op l)) in
           (match uu____12945 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13050,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13090 = encode_q_body env vars pats body in
             match uu____13090 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13135 =
                     let uu____13146 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13146) in
                   FStar_SMTEncoding_Term.mkForall uu____13135
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13165 = encode_q_body env vars pats body in
             match uu____13165 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13209 =
                   let uu____13210 =
                     let uu____13221 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13221) in
                   FStar_SMTEncoding_Term.mkExists uu____13210
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13209, decls))))
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
  let uu____13319 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13319 with
  | (asym,a) ->
      let uu____13326 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13326 with
       | (xsym,x) ->
           let uu____13333 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13333 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13377 =
                      let uu____13388 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13388, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13377 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13414 =
                      let uu____13421 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13421) in
                    FStar_SMTEncoding_Util.mkApp uu____13414 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13434 =
                    let uu____13437 =
                      let uu____13440 =
                        let uu____13443 =
                          let uu____13444 =
                            let uu____13451 =
                              let uu____13452 =
                                let uu____13463 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13463) in
                              FStar_SMTEncoding_Util.mkForall uu____13452 in
                            (uu____13451, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13444 in
                        let uu____13480 =
                          let uu____13483 =
                            let uu____13484 =
                              let uu____13491 =
                                let uu____13492 =
                                  let uu____13503 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13503) in
                                FStar_SMTEncoding_Util.mkForall uu____13492 in
                              (uu____13491,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13484 in
                          [uu____13483] in
                        uu____13443 :: uu____13480 in
                      xtok_decl :: uu____13440 in
                    xname_decl :: uu____13437 in
                  (xtok1, uu____13434) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13594 =
                    let uu____13607 =
                      let uu____13616 =
                        let uu____13617 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13617 in
                      quant axy uu____13616 in
                    (FStar_Parser_Const.op_Eq, uu____13607) in
                  let uu____13626 =
                    let uu____13641 =
                      let uu____13654 =
                        let uu____13663 =
                          let uu____13664 =
                            let uu____13665 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13665 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13664 in
                        quant axy uu____13663 in
                      (FStar_Parser_Const.op_notEq, uu____13654) in
                    let uu____13674 =
                      let uu____13689 =
                        let uu____13702 =
                          let uu____13711 =
                            let uu____13712 =
                              let uu____13713 =
                                let uu____13718 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13719 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13718, uu____13719) in
                              FStar_SMTEncoding_Util.mkLT uu____13713 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13712 in
                          quant xy uu____13711 in
                        (FStar_Parser_Const.op_LT, uu____13702) in
                      let uu____13728 =
                        let uu____13743 =
                          let uu____13756 =
                            let uu____13765 =
                              let uu____13766 =
                                let uu____13767 =
                                  let uu____13772 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13773 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13772, uu____13773) in
                                FStar_SMTEncoding_Util.mkLTE uu____13767 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13766 in
                            quant xy uu____13765 in
                          (FStar_Parser_Const.op_LTE, uu____13756) in
                        let uu____13782 =
                          let uu____13797 =
                            let uu____13810 =
                              let uu____13819 =
                                let uu____13820 =
                                  let uu____13821 =
                                    let uu____13826 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13827 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13826, uu____13827) in
                                  FStar_SMTEncoding_Util.mkGT uu____13821 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13820 in
                              quant xy uu____13819 in
                            (FStar_Parser_Const.op_GT, uu____13810) in
                          let uu____13836 =
                            let uu____13851 =
                              let uu____13864 =
                                let uu____13873 =
                                  let uu____13874 =
                                    let uu____13875 =
                                      let uu____13880 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13881 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13880, uu____13881) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13875 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13874 in
                                quant xy uu____13873 in
                              (FStar_Parser_Const.op_GTE, uu____13864) in
                            let uu____13890 =
                              let uu____13905 =
                                let uu____13918 =
                                  let uu____13927 =
                                    let uu____13928 =
                                      let uu____13929 =
                                        let uu____13934 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13935 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13934, uu____13935) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13929 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13928 in
                                  quant xy uu____13927 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13918) in
                              let uu____13944 =
                                let uu____13959 =
                                  let uu____13972 =
                                    let uu____13981 =
                                      let uu____13982 =
                                        let uu____13983 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13983 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13982 in
                                    quant qx uu____13981 in
                                  (FStar_Parser_Const.op_Minus, uu____13972) in
                                let uu____13992 =
                                  let uu____14007 =
                                    let uu____14020 =
                                      let uu____14029 =
                                        let uu____14030 =
                                          let uu____14031 =
                                            let uu____14036 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14037 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14036, uu____14037) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14031 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14030 in
                                      quant xy uu____14029 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14020) in
                                  let uu____14046 =
                                    let uu____14061 =
                                      let uu____14074 =
                                        let uu____14083 =
                                          let uu____14084 =
                                            let uu____14085 =
                                              let uu____14090 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14091 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14090, uu____14091) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14085 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14084 in
                                        quant xy uu____14083 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14074) in
                                    let uu____14100 =
                                      let uu____14115 =
                                        let uu____14128 =
                                          let uu____14137 =
                                            let uu____14138 =
                                              let uu____14139 =
                                                let uu____14144 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14145 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14144, uu____14145) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14139 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14138 in
                                          quant xy uu____14137 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14128) in
                                      let uu____14154 =
                                        let uu____14169 =
                                          let uu____14182 =
                                            let uu____14191 =
                                              let uu____14192 =
                                                let uu____14193 =
                                                  let uu____14198 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14199 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14198, uu____14199) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14193 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14192 in
                                            quant xy uu____14191 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14182) in
                                        let uu____14208 =
                                          let uu____14223 =
                                            let uu____14236 =
                                              let uu____14245 =
                                                let uu____14246 =
                                                  let uu____14247 =
                                                    let uu____14252 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14253 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14252,
                                                      uu____14253) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14247 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14246 in
                                              quant xy uu____14245 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14236) in
                                          let uu____14262 =
                                            let uu____14277 =
                                              let uu____14290 =
                                                let uu____14299 =
                                                  let uu____14300 =
                                                    let uu____14301 =
                                                      let uu____14306 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14307 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14306,
                                                        uu____14307) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14301 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14300 in
                                                quant xy uu____14299 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14290) in
                                            let uu____14316 =
                                              let uu____14331 =
                                                let uu____14344 =
                                                  let uu____14353 =
                                                    let uu____14354 =
                                                      let uu____14355 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14355 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14354 in
                                                  quant qx uu____14353 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14344) in
                                              [uu____14331] in
                                            uu____14277 :: uu____14316 in
                                          uu____14223 :: uu____14262 in
                                        uu____14169 :: uu____14208 in
                                      uu____14115 :: uu____14154 in
                                    uu____14061 :: uu____14100 in
                                  uu____14007 :: uu____14046 in
                                uu____13959 :: uu____13992 in
                              uu____13905 :: uu____13944 in
                            uu____13851 :: uu____13890 in
                          uu____13797 :: uu____13836 in
                        uu____13743 :: uu____13782 in
                      uu____13689 :: uu____13728 in
                    uu____13641 :: uu____13674 in
                  uu____13594 :: uu____13626 in
                let mk1 l v1 =
                  let uu____14569 =
                    let uu____14578 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14636  ->
                              match uu____14636 with
                              | (l',uu____14650) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14578
                      (FStar_Option.map
                         (fun uu____14710  ->
                            match uu____14710 with | (uu____14729,b) -> b v1)) in
                  FStar_All.pipe_right uu____14569 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14800  ->
                          match uu____14800 with
                          | (l',uu____14814) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14855 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14855 with
        | (xxsym,xx) ->
            let uu____14862 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14862 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14872 =
                   let uu____14879 =
                     let uu____14880 =
                       let uu____14891 =
                         let uu____14892 =
                           let uu____14897 =
                             let uu____14898 =
                               let uu____14903 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14903) in
                             FStar_SMTEncoding_Util.mkEq uu____14898 in
                           (xx_has_type, uu____14897) in
                         FStar_SMTEncoding_Util.mkImp uu____14892 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14891) in
                     FStar_SMTEncoding_Util.mkForall uu____14880 in
                   let uu____14928 =
                     let uu____14929 =
                       let uu____14930 =
                         let uu____14931 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14931 in
                       Prims.strcat module_name uu____14930 in
                     varops.mk_unique uu____14929 in
                   (uu____14879, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14928) in
                 FStar_SMTEncoding_Util.mkAssume uu____14872)
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
    let uu____14971 =
      let uu____14972 =
        let uu____14979 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14979, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14972 in
    let uu____14982 =
      let uu____14985 =
        let uu____14986 =
          let uu____14993 =
            let uu____14994 =
              let uu____15005 =
                let uu____15006 =
                  let uu____15011 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15011) in
                FStar_SMTEncoding_Util.mkImp uu____15006 in
              ([[typing_pred]], [xx], uu____15005) in
            mkForall_fuel uu____14994 in
          (uu____14993, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14986 in
      [uu____14985] in
    uu____14971 :: uu____14982 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15053 =
      let uu____15054 =
        let uu____15061 =
          let uu____15062 =
            let uu____15073 =
              let uu____15078 =
                let uu____15081 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15081] in
              [uu____15078] in
            let uu____15086 =
              let uu____15087 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15087 tt in
            (uu____15073, [bb], uu____15086) in
          FStar_SMTEncoding_Util.mkForall uu____15062 in
        (uu____15061, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15054 in
    let uu____15108 =
      let uu____15111 =
        let uu____15112 =
          let uu____15119 =
            let uu____15120 =
              let uu____15131 =
                let uu____15132 =
                  let uu____15137 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15137) in
                FStar_SMTEncoding_Util.mkImp uu____15132 in
              ([[typing_pred]], [xx], uu____15131) in
            mkForall_fuel uu____15120 in
          (uu____15119, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15112 in
      [uu____15111] in
    uu____15053 :: uu____15108 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15187 =
        let uu____15188 =
          let uu____15195 =
            let uu____15198 =
              let uu____15201 =
                let uu____15204 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15205 =
                  let uu____15208 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15208] in
                uu____15204 :: uu____15205 in
              tt :: uu____15201 in
            tt :: uu____15198 in
          ("Prims.Precedes", uu____15195) in
        FStar_SMTEncoding_Util.mkApp uu____15188 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15187 in
    let precedes_y_x =
      let uu____15212 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15212 in
    let uu____15215 =
      let uu____15216 =
        let uu____15223 =
          let uu____15224 =
            let uu____15235 =
              let uu____15240 =
                let uu____15243 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15243] in
              [uu____15240] in
            let uu____15248 =
              let uu____15249 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15249 tt in
            (uu____15235, [bb], uu____15248) in
          FStar_SMTEncoding_Util.mkForall uu____15224 in
        (uu____15223, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15216 in
    let uu____15270 =
      let uu____15273 =
        let uu____15274 =
          let uu____15281 =
            let uu____15282 =
              let uu____15293 =
                let uu____15294 =
                  let uu____15299 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15299) in
                FStar_SMTEncoding_Util.mkImp uu____15294 in
              ([[typing_pred]], [xx], uu____15293) in
            mkForall_fuel uu____15282 in
          (uu____15281, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15274 in
      let uu____15324 =
        let uu____15327 =
          let uu____15328 =
            let uu____15335 =
              let uu____15336 =
                let uu____15347 =
                  let uu____15348 =
                    let uu____15353 =
                      let uu____15354 =
                        let uu____15357 =
                          let uu____15360 =
                            let uu____15363 =
                              let uu____15364 =
                                let uu____15369 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15370 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15369, uu____15370) in
                              FStar_SMTEncoding_Util.mkGT uu____15364 in
                            let uu____15371 =
                              let uu____15374 =
                                let uu____15375 =
                                  let uu____15380 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15381 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15380, uu____15381) in
                                FStar_SMTEncoding_Util.mkGTE uu____15375 in
                              let uu____15382 =
                                let uu____15385 =
                                  let uu____15386 =
                                    let uu____15391 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15392 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15391, uu____15392) in
                                  FStar_SMTEncoding_Util.mkLT uu____15386 in
                                [uu____15385] in
                              uu____15374 :: uu____15382 in
                            uu____15363 :: uu____15371 in
                          typing_pred_y :: uu____15360 in
                        typing_pred :: uu____15357 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15354 in
                    (uu____15353, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15348 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15347) in
              mkForall_fuel uu____15336 in
            (uu____15335,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15328 in
        [uu____15327] in
      uu____15273 :: uu____15324 in
    uu____15215 :: uu____15270 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15438 =
      let uu____15439 =
        let uu____15446 =
          let uu____15447 =
            let uu____15458 =
              let uu____15463 =
                let uu____15466 = FStar_SMTEncoding_Term.boxString b in
                [uu____15466] in
              [uu____15463] in
            let uu____15471 =
              let uu____15472 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15472 tt in
            (uu____15458, [bb], uu____15471) in
          FStar_SMTEncoding_Util.mkForall uu____15447 in
        (uu____15446, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15439 in
    let uu____15493 =
      let uu____15496 =
        let uu____15497 =
          let uu____15504 =
            let uu____15505 =
              let uu____15516 =
                let uu____15517 =
                  let uu____15522 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15522) in
                FStar_SMTEncoding_Util.mkImp uu____15517 in
              ([[typing_pred]], [xx], uu____15516) in
            mkForall_fuel uu____15505 in
          (uu____15504, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15497 in
      [uu____15496] in
    uu____15438 :: uu____15493 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15575 =
      let uu____15576 =
        let uu____15583 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15583, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15576 in
    [uu____15575] in
  let mk_and_interp env conj uu____15595 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15620 =
      let uu____15621 =
        let uu____15628 =
          let uu____15629 =
            let uu____15640 =
              let uu____15641 =
                let uu____15646 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15646, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15641 in
            ([[l_and_a_b]], [aa; bb], uu____15640) in
          FStar_SMTEncoding_Util.mkForall uu____15629 in
        (uu____15628, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15621 in
    [uu____15620] in
  let mk_or_interp env disj uu____15684 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15709 =
      let uu____15710 =
        let uu____15717 =
          let uu____15718 =
            let uu____15729 =
              let uu____15730 =
                let uu____15735 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15735, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15730 in
            ([[l_or_a_b]], [aa; bb], uu____15729) in
          FStar_SMTEncoding_Util.mkForall uu____15718 in
        (uu____15717, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15710 in
    [uu____15709] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15798 =
      let uu____15799 =
        let uu____15806 =
          let uu____15807 =
            let uu____15818 =
              let uu____15819 =
                let uu____15824 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15824, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15819 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15818) in
          FStar_SMTEncoding_Util.mkForall uu____15807 in
        (uu____15806, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15799 in
    [uu____15798] in
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
    let uu____15897 =
      let uu____15898 =
        let uu____15905 =
          let uu____15906 =
            let uu____15917 =
              let uu____15918 =
                let uu____15923 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15923, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15918 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15917) in
          FStar_SMTEncoding_Util.mkForall uu____15906 in
        (uu____15905, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15898 in
    [uu____15897] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15994 =
      let uu____15995 =
        let uu____16002 =
          let uu____16003 =
            let uu____16014 =
              let uu____16015 =
                let uu____16020 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16020, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16015 in
            ([[l_imp_a_b]], [aa; bb], uu____16014) in
          FStar_SMTEncoding_Util.mkForall uu____16003 in
        (uu____16002, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15995 in
    [uu____15994] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16083 =
      let uu____16084 =
        let uu____16091 =
          let uu____16092 =
            let uu____16103 =
              let uu____16104 =
                let uu____16109 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16109, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16104 in
            ([[l_iff_a_b]], [aa; bb], uu____16103) in
          FStar_SMTEncoding_Util.mkForall uu____16092 in
        (uu____16091, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16084 in
    [uu____16083] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16161 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16161 in
    let uu____16164 =
      let uu____16165 =
        let uu____16172 =
          let uu____16173 =
            let uu____16184 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16184) in
          FStar_SMTEncoding_Util.mkForall uu____16173 in
        (uu____16172, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16165 in
    [uu____16164] in
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
      let uu____16244 =
        let uu____16251 =
          let uu____16254 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16254] in
        ("Valid", uu____16251) in
      FStar_SMTEncoding_Util.mkApp uu____16244 in
    let uu____16257 =
      let uu____16258 =
        let uu____16265 =
          let uu____16266 =
            let uu____16277 =
              let uu____16278 =
                let uu____16283 =
                  let uu____16284 =
                    let uu____16295 =
                      let uu____16300 =
                        let uu____16303 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16303] in
                      [uu____16300] in
                    let uu____16308 =
                      let uu____16309 =
                        let uu____16314 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16314, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16309 in
                    (uu____16295, [xx1], uu____16308) in
                  FStar_SMTEncoding_Util.mkForall uu____16284 in
                (uu____16283, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16278 in
            ([[l_forall_a_b]], [aa; bb], uu____16277) in
          FStar_SMTEncoding_Util.mkForall uu____16266 in
        (uu____16265, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16258 in
    [uu____16257] in
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
      let uu____16396 =
        let uu____16403 =
          let uu____16406 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16406] in
        ("Valid", uu____16403) in
      FStar_SMTEncoding_Util.mkApp uu____16396 in
    let uu____16409 =
      let uu____16410 =
        let uu____16417 =
          let uu____16418 =
            let uu____16429 =
              let uu____16430 =
                let uu____16435 =
                  let uu____16436 =
                    let uu____16447 =
                      let uu____16452 =
                        let uu____16455 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16455] in
                      [uu____16452] in
                    let uu____16460 =
                      let uu____16461 =
                        let uu____16466 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16466, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16461 in
                    (uu____16447, [xx1], uu____16460) in
                  FStar_SMTEncoding_Util.mkExists uu____16436 in
                (uu____16435, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16430 in
            ([[l_exists_a_b]], [aa; bb], uu____16429) in
          FStar_SMTEncoding_Util.mkForall uu____16418 in
        (uu____16417, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16410 in
    [uu____16409] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16526 =
      let uu____16527 =
        let uu____16534 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16535 = varops.mk_unique "typing_range_const" in
        (uu____16534, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16535) in
      FStar_SMTEncoding_Util.mkAssume uu____16527 in
    [uu____16526] in
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
        let uu____16569 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16569 x1 t in
      let uu____16570 =
        let uu____16581 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16581) in
      FStar_SMTEncoding_Util.mkForall uu____16570 in
    let uu____16604 =
      let uu____16605 =
        let uu____16612 =
          let uu____16613 =
            let uu____16624 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16624) in
          FStar_SMTEncoding_Util.mkForall uu____16613 in
        (uu____16612,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16605 in
    [uu____16604] in
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
          let uu____16948 =
            FStar_Util.find_opt
              (fun uu____16974  ->
                 match uu____16974 with
                 | (l,uu____16986) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16948 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17011,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17050 = encode_function_type_as_formula t env in
        match uu____17050 with
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
              let uu____17096 =
                ((let uu____17099 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____17099) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____17096
              then
                let uu____17106 = new_term_constant_and_tok_from_lid env lid in
                match uu____17106 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17125 =
                        let uu____17126 = FStar_Syntax_Subst.compress t_norm in
                        uu____17126.FStar_Syntax_Syntax.n in
                      match uu____17125 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17132) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17162  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17167 -> [] in
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
                (let uu____17181 = prims.is lid in
                 if uu____17181
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17189 = prims.mk lid vname in
                   match uu____17189 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17213 =
                      let uu____17224 = curried_arrow_formals_comp t_norm in
                      match uu____17224 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17242 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17242
                            then
                              let uu____17243 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___147_17246 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___147_17246.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___147_17246.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___147_17246.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___147_17246.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___147_17246.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___147_17246.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___147_17246.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___147_17246.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___147_17246.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___147_17246.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___147_17246.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___147_17246.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___147_17246.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___147_17246.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___147_17246.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___147_17246.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___147_17246.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___147_17246.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___147_17246.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___147_17246.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___147_17246.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___147_17246.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___147_17246.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___147_17246.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___147_17246.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___147_17246.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___147_17246.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17243
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17258 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17258)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17213 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17303 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17303 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17324 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___119_17366  ->
                                       match uu___119_17366 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17370 =
                                             FStar_Util.prefix vars in
                                           (match uu____17370 with
                                            | (uu____17391,(xxsym,uu____17393))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17411 =
                                                  let uu____17412 =
                                                    let uu____17419 =
                                                      let uu____17420 =
                                                        let uu____17431 =
                                                          let uu____17432 =
                                                            let uu____17437 =
                                                              let uu____17438
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17438 in
                                                            (vapp,
                                                              uu____17437) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17432 in
                                                        ([[vapp]], vars,
                                                          uu____17431) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17420 in
                                                    (uu____17419,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17412 in
                                                [uu____17411])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17457 =
                                             FStar_Util.prefix vars in
                                           (match uu____17457 with
                                            | (uu____17478,(xxsym,uu____17480))
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
                                                let uu____17503 =
                                                  let uu____17504 =
                                                    let uu____17511 =
                                                      let uu____17512 =
                                                        let uu____17523 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17523) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17512 in
                                                    (uu____17511,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17504 in
                                                [uu____17503])
                                       | uu____17540 -> [])) in
                             let uu____17541 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17541 with
                              | (vars,guards,env',decls1,uu____17568) ->
                                  let uu____17581 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17590 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17590, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17592 =
                                          encode_formula p env' in
                                        (match uu____17592 with
                                         | (g,ds) ->
                                             let uu____17603 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17603,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17581 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17616 =
                                           let uu____17623 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17623) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17616 in
                                       let uu____17632 =
                                         let vname_decl =
                                           let uu____17640 =
                                             let uu____17651 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17661  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17651,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17640 in
                                         let uu____17670 =
                                           let env2 =
                                             let uu___148_17676 = env1 in
                                             {
                                               bindings =
                                                 (uu___148_17676.bindings);
                                               depth = (uu___148_17676.depth);
                                               tcenv = (uu___148_17676.tcenv);
                                               warn = (uu___148_17676.warn);
                                               cache = (uu___148_17676.cache);
                                               nolabels =
                                                 (uu___148_17676.nolabels);
                                               use_zfuel_name =
                                                 (uu___148_17676.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___148_17676.current_module_name)
                                             } in
                                           let uu____17677 =
                                             let uu____17678 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17678 in
                                           if uu____17677
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17670 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17693::uu____17694 ->
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
                                                     let uu____17734 =
                                                       let uu____17745 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17745) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17734 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17772 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17775 =
                                               match formals with
                                               | [] ->
                                                   let uu____17792 =
                                                     let uu____17793 =
                                                       let uu____17796 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_41  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_41)
                                                         uu____17796 in
                                                     push_free_var env1 lid
                                                       vname uu____17793 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17792)
                                               | uu____17801 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17808 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17808 in
                                                   let name_tok_corr =
                                                     let uu____17810 =
                                                       let uu____17817 =
                                                         let uu____17818 =
                                                           let uu____17829 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17829) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17818 in
                                                       (uu____17817,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17810 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17775 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17632 with
                                        | (decls2,env2) ->
                                            let uu____17872 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17880 =
                                                encode_term res_t1 env' in
                                              match uu____17880 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17893 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17893, decls) in
                                            (match uu____17872 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17904 =
                                                     let uu____17911 =
                                                       let uu____17912 =
                                                         let uu____17923 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17923) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17912 in
                                                     (uu____17911,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17904 in
                                                 let freshness =
                                                   let uu____17939 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17939
                                                   then
                                                     let uu____17944 =
                                                       let uu____17945 =
                                                         let uu____17956 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17967 =
                                                           varops.next_id () in
                                                         (vname, uu____17956,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17967) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17945 in
                                                     let uu____17970 =
                                                       let uu____17973 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17973] in
                                                     uu____17944 ::
                                                       uu____17970
                                                   else [] in
                                                 let g =
                                                   let uu____17978 =
                                                     let uu____17981 =
                                                       let uu____17984 =
                                                         let uu____17987 =
                                                           let uu____17990 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17990 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17987 in
                                                       FStar_List.append
                                                         decls3 uu____17984 in
                                                     FStar_List.append decls2
                                                       uu____17981 in
                                                   FStar_List.append decls11
                                                     uu____17978 in
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
          let uu____18025 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18025 with
          | FStar_Pervasives_Native.None  ->
              let uu____18062 = encode_free_var false env x t t_norm [] in
              (match uu____18062 with
               | (decls,env1) ->
                   let uu____18089 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18089 with
                    | (n1,x',uu____18116) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18137) ->
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
            let uu____18197 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18197 with
            | (decls,env1) ->
                let uu____18216 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18216
                then
                  let uu____18223 =
                    let uu____18226 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18226 in
                  (uu____18223, env1)
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
             (fun uu____18281  ->
                fun lb  ->
                  match uu____18281 with
                  | (decls,env1) ->
                      let uu____18301 =
                        let uu____18308 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18308
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18301 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18330 = FStar_Syntax_Util.head_and_args t in
    match uu____18330 with
    | (hd1,args) ->
        let uu____18367 =
          let uu____18368 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18368.FStar_Syntax_Syntax.n in
        (match uu____18367 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18372,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18391 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18416  ->
      fun quals  ->
        match uu____18416 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18492 = FStar_Util.first_N nbinders formals in
              match uu____18492 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18573  ->
                         fun uu____18574  ->
                           match (uu____18573, uu____18574) with
                           | ((formal,uu____18592),(binder,uu____18594)) ->
                               let uu____18603 =
                                 let uu____18610 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18610) in
                               FStar_Syntax_Syntax.NT uu____18603) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18618 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18649  ->
                              match uu____18649 with
                              | (x,i) ->
                                  let uu____18660 =
                                    let uu___149_18661 = x in
                                    let uu____18662 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___149_18661.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___149_18661.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18662
                                    } in
                                  (uu____18660, i))) in
                    FStar_All.pipe_right uu____18618
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18680 =
                      let uu____18681 = FStar_Syntax_Subst.compress body in
                      let uu____18682 =
                        let uu____18683 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18683 in
                      FStar_Syntax_Syntax.extend_app_n uu____18681
                        uu____18682 in
                    uu____18680 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18744 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18744
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___150_18747 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___150_18747.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___150_18747.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___150_18747.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___150_18747.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___150_18747.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___150_18747.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___150_18747.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___150_18747.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___150_18747.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___150_18747.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___150_18747.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___150_18747.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___150_18747.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___150_18747.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___150_18747.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___150_18747.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___150_18747.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___150_18747.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___150_18747.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___150_18747.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___150_18747.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___150_18747.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___150_18747.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___150_18747.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___150_18747.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___150_18747.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___150_18747.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18780 = FStar_Syntax_Util.abs_formals e in
                match uu____18780 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18844::uu____18845 ->
                         let uu____18860 =
                           let uu____18861 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18861.FStar_Syntax_Syntax.n in
                         (match uu____18860 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18906 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18906 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18948 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18948
                                   then
                                     let uu____18983 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18983 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19077  ->
                                                   fun uu____19078  ->
                                                     match (uu____19077,
                                                             uu____19078)
                                                     with
                                                     | ((x,uu____19096),
                                                        (b,uu____19098)) ->
                                                         let uu____19107 =
                                                           let uu____19114 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19114) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19107)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19116 =
                                            let uu____19137 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19137) in
                                          (uu____19116, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19205 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19205 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19294) ->
                              let uu____19299 =
                                let uu____19320 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19320 in
                              (uu____19299, true)
                          | uu____19385 when Prims.op_Negation norm1 ->
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
                          | uu____19387 ->
                              let uu____19388 =
                                let uu____19389 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19390 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19389
                                  uu____19390 in
                              failwith uu____19388)
                     | uu____19415 ->
                         let uu____19416 =
                           let uu____19417 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19417.FStar_Syntax_Syntax.n in
                         (match uu____19416 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19462 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19462 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19494 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19494 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19577 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19633 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19633
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19645 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19739  ->
                            fun lb  ->
                              match uu____19739 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19834 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19834
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19837 =
                                      let uu____19852 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19852
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19837 with
                                    | (tok,decl,env2) ->
                                        let uu____19898 =
                                          let uu____19911 =
                                            let uu____19922 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19922, tok) in
                                          uu____19911 :: toks in
                                        (uu____19898, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19645 with
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
                        | uu____20105 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20113 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20113 vars)
                            else
                              (let uu____20115 =
                                 let uu____20122 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20122) in
                               FStar_SMTEncoding_Util.mkApp uu____20115) in
                      let uu____20131 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___120_20135  ->
                                 match uu___120_20135 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____20136 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____20142 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____20142))) in
                      if uu____20131
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____20180;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____20182;
                                FStar_Syntax_Syntax.lbeff = uu____20183;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____20246 =
                                 let uu____20253 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____20253 with
                                 | (tcenv',uu____20271,e_t) ->
                                     let uu____20277 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____20288 -> failwith "Impossible" in
                                     (match uu____20277 with
                                      | (e1,t_norm1) ->
                                          ((let uu___153_20304 = env1 in
                                            {
                                              bindings =
                                                (uu___153_20304.bindings);
                                              depth = (uu___153_20304.depth);
                                              tcenv = tcenv';
                                              warn = (uu___153_20304.warn);
                                              cache = (uu___153_20304.cache);
                                              nolabels =
                                                (uu___153_20304.nolabels);
                                              use_zfuel_name =
                                                (uu___153_20304.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___153_20304.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___153_20304.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____20246 with
                                | (env',e1,t_norm1) ->
                                    let uu____20314 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____20314 with
                                     | ((binders,body,uu____20335,uu____20336),curry)
                                         ->
                                         ((let uu____20347 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____20347
                                           then
                                             let uu____20348 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____20349 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____20348 uu____20349
                                           else ());
                                          (let uu____20351 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____20351 with
                                           | (vars,guards,env'1,binder_decls,uu____20378)
                                               ->
                                               let body1 =
                                                 let uu____20392 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____20392
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____20395 =
                                                 let uu____20404 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____20404
                                                 then
                                                   let uu____20415 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____20416 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____20415, uu____20416)
                                                 else
                                                   (let uu____20426 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____20426)) in
                                               (match uu____20395 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____20449 =
                                                        let uu____20456 =
                                                          let uu____20457 =
                                                            let uu____20468 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____20468) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____20457 in
                                                        let uu____20479 =
                                                          let uu____20482 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____20482 in
                                                        (uu____20456,
                                                          uu____20479,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____20449 in
                                                    let uu____20485 =
                                                      let uu____20488 =
                                                        let uu____20491 =
                                                          let uu____20494 =
                                                            let uu____20497 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____20497 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____20494 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____20491 in
                                                      FStar_List.append
                                                        decls1 uu____20488 in
                                                    (uu____20485, env1))))))
                           | uu____20502 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____20537 = varops.fresh "fuel" in
                             (uu____20537, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____20540 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____20628  ->
                                     fun uu____20629  ->
                                       match (uu____20628, uu____20629) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____20777 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____20777 in
                                           let gtok =
                                             let uu____20779 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____20779 in
                                           let env3 =
                                             let uu____20781 =
                                               let uu____20784 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_42  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_42) uu____20784 in
                                             push_free_var env2 flid gtok
                                               uu____20781 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____20540 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____20940
                                 t_norm uu____20942 =
                                 match (uu____20940, uu____20942) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____20986;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____20987;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____21015 =
                                       let uu____21022 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____21022 with
                                       | (tcenv',uu____21044,e_t) ->
                                           let uu____21050 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____21061 ->
                                                 failwith "Impossible" in
                                           (match uu____21050 with
                                            | (e1,t_norm1) ->
                                                ((let uu___154_21077 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___154_21077.bindings);
                                                    depth =
                                                      (uu___154_21077.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___154_21077.warn);
                                                    cache =
                                                      (uu___154_21077.cache);
                                                    nolabels =
                                                      (uu___154_21077.nolabels);
                                                    use_zfuel_name =
                                                      (uu___154_21077.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___154_21077.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___154_21077.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____21015 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____21092 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____21092
                                            then
                                              let uu____21093 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____21094 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____21095 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____21093 uu____21094
                                                uu____21095
                                            else ());
                                           (let uu____21097 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____21097 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____21134 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____21134
                                                  then
                                                    let uu____21135 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____21136 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____21137 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____21138 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____21135 uu____21136
                                                      uu____21137 uu____21138
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____21142 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____21142 with
                                                  | (vars,guards,env'1,binder_decls,uu____21173)
                                                      ->
                                                      let decl_g =
                                                        let uu____21187 =
                                                          let uu____21198 =
                                                            let uu____21201 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____21201 in
                                                          (g, uu____21198,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____21187 in
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
                                                        let uu____21226 =
                                                          let uu____21233 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____21233) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21226 in
                                                      let gsapp =
                                                        let uu____21243 =
                                                          let uu____21250 =
                                                            let uu____21253 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____21253 ::
                                                              vars_tm in
                                                          (g, uu____21250) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21243 in
                                                      let gmax =
                                                        let uu____21259 =
                                                          let uu____21266 =
                                                            let uu____21269 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____21269 ::
                                                              vars_tm in
                                                          (g, uu____21266) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21259 in
                                                      let body1 =
                                                        let uu____21275 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____21275
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____21277 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____21277 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____21295
                                                               =
                                                               let uu____21302
                                                                 =
                                                                 let uu____21303
                                                                   =
                                                                   let uu____21318
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
                                                                    uu____21318) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____21303 in
                                                               let uu____21339
                                                                 =
                                                                 let uu____21342
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____21342 in
                                                               (uu____21302,
                                                                 uu____21339,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21295 in
                                                           let eqn_f =
                                                             let uu____21346
                                                               =
                                                               let uu____21353
                                                                 =
                                                                 let uu____21354
                                                                   =
                                                                   let uu____21365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____21365) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21354 in
                                                               (uu____21353,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21346 in
                                                           let eqn_g' =
                                                             let uu____21379
                                                               =
                                                               let uu____21386
                                                                 =
                                                                 let uu____21387
                                                                   =
                                                                   let uu____21398
                                                                    =
                                                                    let uu____21399
                                                                    =
                                                                    let uu____21404
                                                                    =
                                                                    let uu____21405
                                                                    =
                                                                    let uu____21412
                                                                    =
                                                                    let uu____21415
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21415
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21412) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21405 in
                                                                    (gsapp,
                                                                    uu____21404) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____21399 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____21398) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21387 in
                                                               (uu____21386,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21379 in
                                                           let uu____21438 =
                                                             let uu____21447
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____21447
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____21476)
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
                                                                    let uu____21501
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____21501
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____21506
                                                                    =
                                                                    let uu____21513
                                                                    =
                                                                    let uu____21514
                                                                    =
                                                                    let uu____21525
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21525) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21514 in
                                                                    (uu____21513,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21506 in
                                                                 let uu____21546
                                                                   =
                                                                   let uu____21553
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____21553
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____21566
                                                                    =
                                                                    let uu____21569
                                                                    =
                                                                    let uu____21570
                                                                    =
                                                                    let uu____21577
                                                                    =
                                                                    let uu____21578
                                                                    =
                                                                    let uu____21589
                                                                    =
                                                                    let uu____21590
                                                                    =
                                                                    let uu____21595
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21595,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21590 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21589) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21578 in
                                                                    (uu____21577,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21570 in
                                                                    [uu____21569] in
                                                                    (d3,
                                                                    uu____21566) in
                                                                 (match uu____21546
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____21438
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
                               let uu____21660 =
                                 let uu____21673 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____21752  ->
                                      fun uu____21753  ->
                                        match (uu____21752, uu____21753) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____21908 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____21908 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____21673 in
                               (match uu____21660 with
                                | (decls2,eqns,env01) ->
                                    let uu____21981 =
                                      let isDeclFun uu___121_21993 =
                                        match uu___121_21993 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____21994 -> true
                                        | uu____22005 -> false in
                                      let uu____22006 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____22006
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____21981 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22057 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22057
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
        let uu____22106 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22106 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22110 = encode_sigelt' env se in
      match uu____22110 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22126 =
                  let uu____22127 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22127 in
                [uu____22126]
            | uu____22128 ->
                let uu____22129 =
                  let uu____22132 =
                    let uu____22133 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22133 in
                  uu____22132 :: g in
                let uu____22134 =
                  let uu____22137 =
                    let uu____22138 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22138 in
                  [uu____22137] in
                FStar_List.append uu____22129 uu____22134 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22151 =
          let uu____22152 = FStar_Syntax_Subst.compress t in
          uu____22152.FStar_Syntax_Syntax.n in
        match uu____22151 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22156)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____22161 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22166 =
          let uu____22167 = FStar_Syntax_Subst.compress t in
          uu____22167.FStar_Syntax_Syntax.n in
        match uu____22166 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22171)) ->
            (FStar_Util.string_of_bytes bytes) = "uninterpreted_by_smt"
        | uu____22176 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22181 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22186 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22189 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22192 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22207 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22211 =
            let uu____22212 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22212 Prims.op_Negation in
          if uu____22211
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22238 ->
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
               let uu____22258 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22258 with
               | (aname,atok,env2) ->
                   let uu____22274 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22274 with
                    | (formals,uu____22292) ->
                        let uu____22305 =
                          let uu____22310 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22310 env2 in
                        (match uu____22305 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22322 =
                                 let uu____22323 =
                                   let uu____22334 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22350  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22334,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22323 in
                               [uu____22322;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22363 =
                               let aux uu____22415 uu____22416 =
                                 match (uu____22415, uu____22416) with
                                 | ((bv,uu____22468),(env3,acc_sorts,acc)) ->
                                     let uu____22506 = gen_term_var env3 bv in
                                     (match uu____22506 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22363 with
                              | (uu____22578,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22601 =
                                      let uu____22608 =
                                        let uu____22609 =
                                          let uu____22620 =
                                            let uu____22621 =
                                              let uu____22626 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22626) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22621 in
                                          ([[app]], xs_sorts, uu____22620) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22609 in
                                      (uu____22608,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22601 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22646 =
                                      let uu____22653 =
                                        let uu____22654 =
                                          let uu____22665 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22665) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22654 in
                                      (uu____22653,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22646 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22684 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22684 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22712,uu____22713)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22714 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22714 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22731,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22737 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___122_22741  ->
                      match uu___122_22741 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22742 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22747 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22748 -> false)) in
            Prims.op_Negation uu____22737 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22757 =
               let uu____22764 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22764 env fv t quals in
             match uu____22757 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22779 =
                   let uu____22782 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22782 in
                 (uu____22779, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22790 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22790 with
           | (uu____22799,f1) ->
               let uu____22801 = encode_formula f1 env in
               (match uu____22801 with
                | (f2,decls) ->
                    let g =
                      let uu____22815 =
                        let uu____22816 =
                          let uu____22823 =
                            let uu____22826 =
                              let uu____22827 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22827 in
                            FStar_Pervasives_Native.Some uu____22826 in
                          let uu____22828 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22823, uu____22828) in
                        FStar_SMTEncoding_Util.mkAssume uu____22816 in
                      [uu____22815] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22834) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22846 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22864 =
                       let uu____22867 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22867.FStar_Syntax_Syntax.fv_name in
                     uu____22864.FStar_Syntax_Syntax.v in
                   let uu____22868 =
                     let uu____22869 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22869 in
                   if uu____22868
                   then
                     let val_decl =
                       let uu___155_22897 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___155_22897.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___155_22897.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___155_22897.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22902 = encode_sigelt' env1 val_decl in
                     match uu____22902 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22846 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22930,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22932;
                          FStar_Syntax_Syntax.lbtyp = uu____22933;
                          FStar_Syntax_Syntax.lbeff = uu____22934;
                          FStar_Syntax_Syntax.lbdef = uu____22935;_}::[]),uu____22936)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22955 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22955 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22984 =
                   let uu____22987 =
                     let uu____22988 =
                       let uu____22995 =
                         let uu____22996 =
                           let uu____23007 =
                             let uu____23008 =
                               let uu____23013 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23013) in
                             FStar_SMTEncoding_Util.mkEq uu____23008 in
                           ([[b2t_x]], [xx], uu____23007) in
                         FStar_SMTEncoding_Util.mkForall uu____22996 in
                       (uu____22995,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22988 in
                   [uu____22987] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22984 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23046,uu____23047) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___123_23056  ->
                  match uu___123_23056 with
                  | FStar_Syntax_Syntax.Discriminator uu____23057 -> true
                  | uu____23058 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23061,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23072 =
                     let uu____23073 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23073.FStar_Ident.idText in
                   uu____23072 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___124_23077  ->
                     match uu___124_23077 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23078 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23082) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_23099  ->
                  match uu___125_23099 with
                  | FStar_Syntax_Syntax.Projector uu____23100 -> true
                  | uu____23105 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23108 = try_lookup_free_var env l in
          (match uu____23108 with
           | FStar_Pervasives_Native.Some uu____23115 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___156_23119 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___156_23119.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___156_23119.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___156_23119.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23126) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23144) ->
          let uu____23153 = encode_sigelts env ses in
          (match uu____23153 with
           | (g,env1) ->
               let uu____23170 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___126_23193  ->
                         match uu___126_23193 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23194;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23195;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23196;_}
                             -> false
                         | uu____23199 -> true)) in
               (match uu____23170 with
                | (g',inversions) ->
                    let uu____23214 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___127_23235  ->
                              match uu___127_23235 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23236 ->
                                  true
                              | uu____23247 -> false)) in
                    (match uu____23214 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23265,tps,k,uu____23268,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___128_23285  ->
                    match uu___128_23285 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23286 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23295 = c in
              match uu____23295 with
              | (name,args,uu____23300,uu____23301,uu____23302) ->
                  let uu____23307 =
                    let uu____23308 =
                      let uu____23319 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23336  ->
                                match uu____23336 with
                                | (uu____23343,sort,uu____23345) -> sort)) in
                      (name, uu____23319, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23308 in
                  [uu____23307]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23372 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23378 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23378 FStar_Option.isNone)) in
            if uu____23372
            then []
            else
              (let uu____23410 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23410 with
               | (xxsym,xx) ->
                   let uu____23419 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23458  ->
                             fun l  ->
                               match uu____23458 with
                               | (out,decls) ->
                                   let uu____23478 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23478 with
                                    | (uu____23489,data_t) ->
                                        let uu____23491 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23491 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23537 =
                                                 let uu____23538 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23538.FStar_Syntax_Syntax.n in
                                               match uu____23537 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23549,indices) ->
                                                   indices
                                               | uu____23571 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23595  ->
                                                         match uu____23595
                                                         with
                                                         | (x,uu____23601) ->
                                                             let uu____23602
                                                               =
                                                               let uu____23603
                                                                 =
                                                                 let uu____23610
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23610,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23603 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23602)
                                                    env) in
                                             let uu____23613 =
                                               encode_args indices env1 in
                                             (match uu____23613 with
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
                                                      let uu____23639 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23655
                                                                 =
                                                                 let uu____23660
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23660,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23655)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23639
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23663 =
                                                      let uu____23664 =
                                                        let uu____23669 =
                                                          let uu____23670 =
                                                            let uu____23675 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23675,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23670 in
                                                        (out, uu____23669) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23664 in
                                                    (uu____23663,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23419 with
                    | (data_ax,decls) ->
                        let uu____23688 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23688 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23699 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23699 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23703 =
                                 let uu____23710 =
                                   let uu____23711 =
                                     let uu____23722 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23737 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23722,
                                       uu____23737) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23711 in
                                 let uu____23752 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23710,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23752) in
                               FStar_SMTEncoding_Util.mkAssume uu____23703 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23755 =
            let uu____23768 =
              let uu____23769 = FStar_Syntax_Subst.compress k in
              uu____23769.FStar_Syntax_Syntax.n in
            match uu____23768 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23814 -> (tps, k) in
          (match uu____23755 with
           | (formals,res) ->
               let uu____23837 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23837 with
                | (formals1,res1) ->
                    let uu____23848 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23848 with
                     | (vars,guards,env',binder_decls,uu____23873) ->
                         let uu____23886 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23886 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23905 =
                                  let uu____23912 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23912) in
                                FStar_SMTEncoding_Util.mkApp uu____23905 in
                              let uu____23921 =
                                let tname_decl =
                                  let uu____23931 =
                                    let uu____23932 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23964  ->
                                              match uu____23964 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23977 = varops.next_id () in
                                    (tname, uu____23932,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23977, false) in
                                  constructor_or_logic_type_decl uu____23931 in
                                let uu____23986 =
                                  match vars with
                                  | [] ->
                                      let uu____23999 =
                                        let uu____24000 =
                                          let uu____24003 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____24003 in
                                        push_free_var env1 t tname
                                          uu____24000 in
                                      ([], uu____23999)
                                  | uu____24010 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24019 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24019 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24033 =
                                          let uu____24040 =
                                            let uu____24041 =
                                              let uu____24056 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24056) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24041 in
                                          (uu____24040,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24033 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23986 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23921 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24096 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24096 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24114 =
                                               let uu____24115 =
                                                 let uu____24122 =
                                                   let uu____24123 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24123 in
                                                 (uu____24122,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24115 in
                                             [uu____24114]
                                           else [] in
                                         let uu____24127 =
                                           let uu____24130 =
                                             let uu____24133 =
                                               let uu____24134 =
                                                 let uu____24141 =
                                                   let uu____24142 =
                                                     let uu____24153 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24153) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24142 in
                                                 (uu____24141,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24134 in
                                             [uu____24133] in
                                           FStar_List.append karr uu____24130 in
                                         FStar_List.append decls1 uu____24127 in
                                   let aux =
                                     let uu____24169 =
                                       let uu____24172 =
                                         inversion_axioms tapp vars in
                                       let uu____24175 =
                                         let uu____24178 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24178] in
                                       FStar_List.append uu____24172
                                         uu____24175 in
                                     FStar_List.append kindingAx uu____24169 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24185,uu____24186,uu____24187,uu____24188,uu____24189)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24197,t,uu____24199,n_tps,uu____24201) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24209 = new_term_constant_and_tok_from_lid env d in
          (match uu____24209 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24226 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24226 with
                | (formals,t_res) ->
                    let uu____24261 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24261 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24275 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24275 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24345 =
                                            mk_term_projector_name d x in
                                          (uu____24345,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24347 =
                                  let uu____24366 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24366, true) in
                                FStar_All.pipe_right uu____24347
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
                              let uu____24405 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24405 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24417::uu____24418 ->
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
                                         let uu____24463 =
                                           let uu____24474 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24474) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24463
                                     | uu____24499 -> tok_typing in
                                   let uu____24508 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24508 with
                                    | (vars',guards',env'',decls_formals,uu____24533)
                                        ->
                                        let uu____24546 =
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
                                        (match uu____24546 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24577 ->
                                                   let uu____24584 =
                                                     let uu____24585 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24585 in
                                                   [uu____24584] in
                                             let encode_elim uu____24595 =
                                               let uu____24596 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24596 with
                                               | (head1,args) ->
                                                   let uu____24639 =
                                                     let uu____24640 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24640.FStar_Syntax_Syntax.n in
                                                   (match uu____24639 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24650;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24651;_},uu____24652)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24658 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24658
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
                                                                 | uu____24701
                                                                    ->
                                                                    let uu____24702
                                                                    =
                                                                    let uu____24703
                                                                    =
                                                                    let uu____24708
                                                                    =
                                                                    let uu____24709
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24709 in
                                                                    (uu____24708,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24703 in
                                                                    FStar_Exn.raise
                                                                    uu____24702 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24725
                                                                    =
                                                                    let uu____24726
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24726 in
                                                                    if
                                                                    uu____24725
                                                                    then
                                                                    let uu____24739
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24739]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24741
                                                               =
                                                               let uu____24754
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24804
                                                                     ->
                                                                    fun
                                                                    uu____24805
                                                                     ->
                                                                    match 
                                                                    (uu____24804,
                                                                    uu____24805)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24900
                                                                    =
                                                                    let uu____24907
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24907 in
                                                                    (match uu____24900
                                                                    with
                                                                    | 
                                                                    (uu____24920,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24928
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24928
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24930
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24930
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
                                                                 uu____24754 in
                                                             (match uu____24741
                                                              with
                                                              | (uu____24945,arg_vars,elim_eqns_or_guards,uu____24948)
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
                                                                    let uu____24978
                                                                    =
                                                                    let uu____24985
                                                                    =
                                                                    let uu____24986
                                                                    =
                                                                    let uu____24997
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25008
                                                                    =
                                                                    let uu____25009
                                                                    =
                                                                    let uu____25014
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25014) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25009 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24997,
                                                                    uu____25008) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24986 in
                                                                    (uu____24985,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24978 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25037
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25037,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25039
                                                                    =
                                                                    let uu____25046
                                                                    =
                                                                    let uu____25047
                                                                    =
                                                                    let uu____25058
                                                                    =
                                                                    let uu____25063
                                                                    =
                                                                    let uu____25066
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25066] in
                                                                    [uu____25063] in
                                                                    let uu____25071
                                                                    =
                                                                    let uu____25072
                                                                    =
                                                                    let uu____25077
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25078
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25077,
                                                                    uu____25078) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25072 in
                                                                    (uu____25058,
                                                                    [x],
                                                                    uu____25071) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25047 in
                                                                    let uu____25097
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25046,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25097) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25039
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25104
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
                                                                    (let uu____25132
                                                                    =
                                                                    let uu____25133
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25133
                                                                    dapp1 in
                                                                    [uu____25132]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25104
                                                                    FStar_List.flatten in
                                                                    let uu____25140
                                                                    =
                                                                    let uu____25147
                                                                    =
                                                                    let uu____25148
                                                                    =
                                                                    let uu____25159
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25171
                                                                    =
                                                                    let uu____25176
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25176) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25171 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25159,
                                                                    uu____25170) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25148 in
                                                                    (uu____25147,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25140) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25197 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25197
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
                                                                 | uu____25240
                                                                    ->
                                                                    let uu____25241
                                                                    =
                                                                    let uu____25242
                                                                    =
                                                                    let uu____25247
                                                                    =
                                                                    let uu____25248
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25248 in
                                                                    (uu____25247,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25242 in
                                                                    FStar_Exn.raise
                                                                    uu____25241 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25264
                                                                    =
                                                                    let uu____25265
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25265 in
                                                                    if
                                                                    uu____25264
                                                                    then
                                                                    let uu____25278
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25278]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25280
                                                               =
                                                               let uu____25293
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25343
                                                                     ->
                                                                    fun
                                                                    uu____25344
                                                                     ->
                                                                    match 
                                                                    (uu____25343,
                                                                    uu____25344)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25439
                                                                    =
                                                                    let uu____25446
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25446 in
                                                                    (match uu____25439
                                                                    with
                                                                    | 
                                                                    (uu____25459,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25467
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25467
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25469
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25469
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
                                                                 uu____25293 in
                                                             (match uu____25280
                                                              with
                                                              | (uu____25484,arg_vars,elim_eqns_or_guards,uu____25487)
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
                                                                    let uu____25517
                                                                    =
                                                                    let uu____25524
                                                                    =
                                                                    let uu____25525
                                                                    =
                                                                    let uu____25536
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25547
                                                                    =
                                                                    let uu____25548
                                                                    =
                                                                    let uu____25553
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25553) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25548 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25536,
                                                                    uu____25547) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25525 in
                                                                    (uu____25524,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25517 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25576
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25576,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25578
                                                                    =
                                                                    let uu____25585
                                                                    =
                                                                    let uu____25586
                                                                    =
                                                                    let uu____25597
                                                                    =
                                                                    let uu____25602
                                                                    =
                                                                    let uu____25605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25605] in
                                                                    [uu____25602] in
                                                                    let uu____25610
                                                                    =
                                                                    let uu____25611
                                                                    =
                                                                    let uu____25616
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25617
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25616,
                                                                    uu____25617) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25611 in
                                                                    (uu____25597,
                                                                    [x],
                                                                    uu____25610) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25586 in
                                                                    let uu____25636
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25585,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25636) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25578
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25643
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
                                                                    (let uu____25671
                                                                    =
                                                                    let uu____25672
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25672
                                                                    dapp1 in
                                                                    [uu____25671]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25643
                                                                    FStar_List.flatten in
                                                                    let uu____25679
                                                                    =
                                                                    let uu____25686
                                                                    =
                                                                    let uu____25687
                                                                    =
                                                                    let uu____25698
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25710
                                                                    =
                                                                    let uu____25715
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25715) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25710 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25698,
                                                                    uu____25709) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25687 in
                                                                    (uu____25686,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25679) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25734 ->
                                                        ((let uu____25736 =
                                                            let uu____25737 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25738 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25737
                                                              uu____25738 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25736);
                                                         ([], []))) in
                                             let uu____25743 = encode_elim () in
                                             (match uu____25743 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25763 =
                                                      let uu____25766 =
                                                        let uu____25769 =
                                                          let uu____25772 =
                                                            let uu____25775 =
                                                              let uu____25776
                                                                =
                                                                let uu____25787
                                                                  =
                                                                  let uu____25790
                                                                    =
                                                                    let uu____25791
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25791 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25790 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25787) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25776 in
                                                            [uu____25775] in
                                                          let uu____25796 =
                                                            let uu____25799 =
                                                              let uu____25802
                                                                =
                                                                let uu____25805
                                                                  =
                                                                  let uu____25808
                                                                    =
                                                                    let uu____25811
                                                                    =
                                                                    let uu____25814
                                                                    =
                                                                    let uu____25815
                                                                    =
                                                                    let uu____25822
                                                                    =
                                                                    let uu____25823
                                                                    =
                                                                    let uu____25834
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25834) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25823 in
                                                                    (uu____25822,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25815 in
                                                                    let uu____25847
                                                                    =
                                                                    let uu____25850
                                                                    =
                                                                    let uu____25851
                                                                    =
                                                                    let uu____25858
                                                                    =
                                                                    let uu____25859
                                                                    =
                                                                    let uu____25870
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25881
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25870,
                                                                    uu____25881) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25859 in
                                                                    (uu____25858,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25851 in
                                                                    [uu____25850] in
                                                                    uu____25814
                                                                    ::
                                                                    uu____25847 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25811 in
                                                                  FStar_List.append
                                                                    uu____25808
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25805 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25802 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25799 in
                                                          FStar_List.append
                                                            uu____25772
                                                            uu____25796 in
                                                        FStar_List.append
                                                          decls3 uu____25769 in
                                                      FStar_List.append
                                                        decls2 uu____25766 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25763 in
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
           (fun uu____25927  ->
              fun se  ->
                match uu____25927 with
                | (g,env1) ->
                    let uu____25947 = encode_sigelt env1 se in
                    (match uu____25947 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26006 =
        match uu____26006 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26038 ->
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
                 ((let uu____26044 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26044
                   then
                     let uu____26045 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26046 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26047 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26045 uu____26046 uu____26047
                   else ());
                  (let uu____26049 = encode_term t1 env1 in
                   match uu____26049 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26065 =
                         let uu____26072 =
                           let uu____26073 =
                             let uu____26074 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26074
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26073 in
                         new_term_constant_from_string env1 x uu____26072 in
                       (match uu____26065 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26090 = FStar_Options.log_queries () in
                              if uu____26090
                              then
                                let uu____26093 =
                                  let uu____26094 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26095 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26096 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26094 uu____26095 uu____26096 in
                                FStar_Pervasives_Native.Some uu____26093
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26112,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26126 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26126 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26149,se,uu____26151) ->
                 let uu____26156 = encode_sigelt env1 se in
                 (match uu____26156 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26173,se) ->
                 let uu____26179 = encode_sigelt env1 se in
                 (match uu____26179 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26196 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26196 with | (uu____26219,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26234 'Auu____26235 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26235,'Auu____26234)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26303  ->
              match uu____26303 with
              | (l,uu____26315,uu____26316) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26362  ->
              match uu____26362 with
              | (l,uu____26376,uu____26377) ->
                  let uu____26386 =
                    FStar_All.pipe_left
                      (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26387 =
                    let uu____26390 =
                      let uu____26391 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26391 in
                    [uu____26390] in
                  uu____26386 :: uu____26387)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26413 =
      let uu____26416 =
        let uu____26417 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26420 =
          let uu____26421 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26421 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26417;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26420
        } in
      [uu____26416] in
    FStar_ST.op_Colon_Equals last_env uu____26413
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26448 = FStar_ST.op_Bang last_env in
      match uu____26448 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26470 ->
          let uu___157_26473 = e in
          let uu____26474 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___157_26473.bindings);
            depth = (uu___157_26473.depth);
            tcenv;
            warn = (uu___157_26473.warn);
            cache = (uu___157_26473.cache);
            nolabels = (uu___157_26473.nolabels);
            use_zfuel_name = (uu___157_26473.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___157_26473.encode_non_total_function_typ);
            current_module_name = uu____26474
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26479 = FStar_ST.op_Bang last_env in
    match uu____26479 with
    | [] -> failwith "Empty env stack"
    | uu____26500::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26525  ->
    let uu____26526 = FStar_ST.op_Bang last_env in
    match uu____26526 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___158_26555 = hd1 in
          {
            bindings = (uu___158_26555.bindings);
            depth = (uu___158_26555.depth);
            tcenv = (uu___158_26555.tcenv);
            warn = (uu___158_26555.warn);
            cache = refs;
            nolabels = (uu___158_26555.nolabels);
            use_zfuel_name = (uu___158_26555.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_26555.encode_non_total_function_typ);
            current_module_name = (uu___158_26555.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26577  ->
    let uu____26578 = FStar_ST.op_Bang last_env in
    match uu____26578 with
    | [] -> failwith "Popping an empty stack"
    | uu____26599::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____26624  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____26628  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____26632  ->
    let uu____26633 = FStar_ST.op_Bang last_env in
    match uu____26633 with
    | hd1::uu____26655::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26677 -> failwith "Impossible"
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
        | (uu____26742::uu____26743,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___159_26751 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___159_26751.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___159_26751.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___159_26751.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26752 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26769 =
        let uu____26772 =
          let uu____26773 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26773 in
        let uu____26774 = open_fact_db_tags env in uu____26772 :: uu____26774 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26769
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
      let uu____26798 = encode_sigelt env se in
      match uu____26798 with
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
        let uu____26836 = FStar_Options.log_queries () in
        if uu____26836
        then
          let uu____26839 =
            let uu____26840 =
              let uu____26841 =
                let uu____26842 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26842 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26841 in
            FStar_SMTEncoding_Term.Caption uu____26840 in
          uu____26839 :: decls
        else decls in
      let env =
        let uu____26853 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26853 tcenv in
      let uu____26854 = encode_top_level_facts env se in
      match uu____26854 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26868 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26868))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26882 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26882
       then
         let uu____26883 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26883
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26918  ->
                 fun se  ->
                   match uu____26918 with
                   | (g,env2) ->
                       let uu____26938 = encode_top_level_facts env2 se in
                       (match uu____26938 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26961 =
         encode_signature
           (let uu___160_26970 = env in
            {
              bindings = (uu___160_26970.bindings);
              depth = (uu___160_26970.depth);
              tcenv = (uu___160_26970.tcenv);
              warn = false;
              cache = (uu___160_26970.cache);
              nolabels = (uu___160_26970.nolabels);
              use_zfuel_name = (uu___160_26970.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_26970.encode_non_total_function_typ);
              current_module_name = (uu___160_26970.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26961 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26987 = FStar_Options.log_queries () in
             if uu____26987
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___161_26995 = env1 in
               {
                 bindings = (uu___161_26995.bindings);
                 depth = (uu___161_26995.depth);
                 tcenv = (uu___161_26995.tcenv);
                 warn = true;
                 cache = (uu___161_26995.cache);
                 nolabels = (uu___161_26995.nolabels);
                 use_zfuel_name = (uu___161_26995.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_26995.encode_non_total_function_typ);
                 current_module_name = (uu___161_26995.current_module_name)
               });
            (let uu____26997 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26997
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
        (let uu____27052 =
           let uu____27053 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27053.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27052);
        (let env =
           let uu____27055 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27055 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27067 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27102 = aux rest in
                 (match uu____27102 with
                  | (out,rest1) ->
                      let t =
                        let uu____27132 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27132 with
                        | FStar_Pervasives_Native.Some uu____27137 ->
                            let uu____27138 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27138
                              x.FStar_Syntax_Syntax.sort
                        | uu____27139 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27143 =
                        let uu____27146 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_27149 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_27149.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_27149.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27146 :: out in
                      (uu____27143, rest1))
             | uu____27154 -> ([], bindings1) in
           let uu____27161 = aux bindings in
           match uu____27161 with
           | (closing,bindings1) ->
               let uu____27186 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27186, bindings1) in
         match uu____27067 with
         | (q1,bindings1) ->
             let uu____27209 =
               let uu____27214 =
                 FStar_List.filter
                   (fun uu___129_27219  ->
                      match uu___129_27219 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27220 ->
                          false
                      | uu____27227 -> true) bindings1 in
               encode_env_bindings env uu____27214 in
             (match uu____27209 with
              | (env_decls,env1) ->
                  ((let uu____27245 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27245
                    then
                      let uu____27246 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27246
                    else ());
                   (let uu____27248 = encode_formula q1 env1 in
                    match uu____27248 with
                    | (phi,qdecls) ->
                        let uu____27269 =
                          let uu____27274 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27274 phi in
                        (match uu____27269 with
                         | (labels,phi1) ->
                             let uu____27291 = encode_labels labels in
                             (match uu____27291 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27328 =
                                      let uu____27335 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27336 =
                                        varops.mk_unique "@query" in
                                      (uu____27335,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27336) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27328 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____27355 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27355 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27357 = encode_formula q env in
       match uu____27357 with
       | (f,uu____27363) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27365) -> true
             | uu____27370 -> false)))