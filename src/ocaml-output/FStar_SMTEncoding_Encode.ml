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
  let new_scope uu____718 =
    let uu____719 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____722 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____719, uu____722) in
  let scopes =
    let uu____742 = let uu____753 = new_scope () in [uu____753] in
    FStar_Util.mk_ref uu____742 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____794 =
        let uu____797 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____797
          (fun uu____899  ->
             match uu____899 with
             | (names1,uu____911) -> FStar_Util.smap_try_find names1 y1) in
      match uu____794 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____920 ->
          (FStar_Util.incr ctr;
           (let uu____943 =
              let uu____944 =
                let uu____945 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____945 in
              Prims.strcat "__" uu____944 in
            Prims.strcat y1 uu____943)) in
    let top_scope =
      let uu____1009 =
        let uu____1018 = FStar_ST.op_Bang scopes in FStar_List.hd uu____1018 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1009 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1146 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1233 =
      let uu____1234 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1234 in
    FStar_Util.format2 "%s_%s" pfx uu____1233 in
  let string_const s =
    let uu____1239 =
      let uu____1242 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1242
        (fun uu____1344  ->
           match uu____1344 with
           | (uu____1355,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1239 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1368 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1368 in
        let top_scope =
          let uu____1372 =
            let uu____1381 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1381 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1372 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1498 =
    let uu____1499 =
      let uu____1510 = new_scope () in
      let uu____1519 = FStar_ST.op_Bang scopes in uu____1510 :: uu____1519 in
    FStar_ST.op_Colon_Equals scopes uu____1499 in
  let pop1 uu____1701 =
    let uu____1702 =
      let uu____1713 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1713 in
    FStar_ST.op_Colon_Equals scopes uu____1702 in
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
    let uu___133_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___133_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___133_1896.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1931 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1969 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____2020 'Auu____2021 .
    'Auu____2021 ->
      ('Auu____2021,'Auu____2020 FStar_Pervasives_Native.option)
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
  'Auu____2335 .
    'Auu____2335 ->
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
                 (fun uu___109_2369  ->
                    match uu___109_2369 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2373 -> [])) in
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
    let uu____2384 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___110_2394  ->
              match uu___110_2394 with
              | Binding_var (x,uu____2396) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2398,uu____2399,uu____2400) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2384 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2417 .
    env_t ->
      (binding -> 'Auu____2417 FStar_Pervasives_Native.option) ->
        'Auu____2417 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2447 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2447
      then
        let uu____2450 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2450
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
      let uu____2465 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2465)
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
        (let uu___134_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___134_2483.tcenv);
           warn = (uu___134_2483.warn);
           cache = (uu___134_2483.cache);
           nolabels = (uu___134_2483.nolabels);
           use_zfuel_name = (uu___134_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___134_2483.encode_non_total_function_typ);
           current_module_name = (uu___134_2483.current_module_name)
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
        (let uu___135_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___135_2503.depth);
           tcenv = (uu___135_2503.tcenv);
           warn = (uu___135_2503.warn);
           cache = (uu___135_2503.cache);
           nolabels = (uu___135_2503.nolabels);
           use_zfuel_name = (uu___135_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___135_2503.encode_non_total_function_typ);
           current_module_name = (uu___135_2503.current_module_name)
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
          (let uu___136_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___136_2527.depth);
             tcenv = (uu___136_2527.tcenv);
             warn = (uu___136_2527.warn);
             cache = (uu___136_2527.cache);
             nolabels = (uu___136_2527.nolabels);
             use_zfuel_name = (uu___136_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___136_2527.encode_non_total_function_typ);
             current_module_name = (uu___136_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___137_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___137_2540.depth);
          tcenv = (uu___137_2540.tcenv);
          warn = (uu___137_2540.warn);
          cache = (uu___137_2540.cache);
          nolabels = (uu___137_2540.nolabels);
          use_zfuel_name = (uu___137_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___137_2540.encode_non_total_function_typ);
          current_module_name = (uu___137_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___111_2566  ->
             match uu___111_2566 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2579 -> FStar_Pervasives_Native.None) in
      let uu____2584 = aux a in
      match uu____2584 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2596 = aux a2 in
          (match uu____2596 with
           | FStar_Pervasives_Native.None  ->
               let uu____2607 =
                 let uu____2608 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2609 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2608 uu____2609 in
               failwith uu____2607
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
      let uu____2638 =
        let uu___138_2639 = env in
        let uu____2640 =
          let uu____2643 =
            let uu____2644 =
              let uu____2657 =
                let uu____2660 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2660 in
              (x, fname, uu____2657, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2644 in
          uu____2643 :: (env.bindings) in
        {
          bindings = uu____2640;
          depth = (uu___138_2639.depth);
          tcenv = (uu___138_2639.tcenv);
          warn = (uu___138_2639.warn);
          cache = (uu___138_2639.cache);
          nolabels = (uu___138_2639.nolabels);
          use_zfuel_name = (uu___138_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___138_2639.encode_non_total_function_typ);
          current_module_name = (uu___138_2639.current_module_name)
        } in
      (fname, ftok, uu____2638)
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
        (fun uu___112_2704  ->
           match uu___112_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___113_2770  ->
             match uu___113_2770 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2785 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2762 FStar_Option.isSome
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
      let uu____2806 = try_lookup_lid env a in
      match uu____2806 with
      | FStar_Pervasives_Native.None  ->
          let uu____2839 =
            let uu____2840 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2840 in
          failwith uu____2839
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
          let uu___139_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___139_2892.depth);
            tcenv = (uu___139_2892.tcenv);
            warn = (uu___139_2892.warn);
            cache = (uu___139_2892.cache);
            nolabels = (uu___139_2892.nolabels);
            use_zfuel_name = (uu___139_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___139_2892.encode_non_total_function_typ);
            current_module_name = (uu___139_2892.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2909 = lookup_lid env x in
        match uu____2909 with
        | (t1,t2,uu____2922) ->
            let t3 =
              let uu____2932 =
                let uu____2939 =
                  let uu____2942 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2942] in
                (f, uu____2939) in
              FStar_SMTEncoding_Util.mkApp uu____2932 in
            let uu___140_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___140_2947.depth);
              tcenv = (uu___140_2947.tcenv);
              warn = (uu___140_2947.warn);
              cache = (uu___140_2947.cache);
              nolabels = (uu___140_2947.nolabels);
              use_zfuel_name = (uu___140_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___140_2947.encode_non_total_function_typ);
              current_module_name = (uu___140_2947.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2962 = try_lookup_lid env l in
      match uu____2962 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3011 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3019,fuel::[]) ->
                         let uu____3023 =
                           let uu____3024 =
                             let uu____3025 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____3025
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____3024 "fuel" in
                         if uu____3023
                         then
                           let uu____3028 =
                             let uu____3029 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3029
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____3028
                         else FStar_Pervasives_Native.Some t
                     | uu____3033 -> FStar_Pervasives_Native.Some t)
                | uu____3034 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3049 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____3049 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3053 =
            let uu____3054 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____3054 in
          failwith uu____3053
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3067 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3067 with | (x,uu____3079,uu____3080) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3107 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____3107 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3143;
                 FStar_SMTEncoding_Term.rng = uu____3144;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3159 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3183 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_3201  ->
           match uu___114_3201 with
           | Binding_fvar (uu____3204,nm',tok,uu____3207) when nm = nm' ->
               tok
           | uu____3216 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3223 .
    'Auu____3223 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3241  ->
      match uu____3241 with
      | (pats,vars,body) ->
          let fallback uu____3266 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3271 = FStar_Options.unthrottle_inductives () in
          if uu____3271
          then fallback ()
          else
            (let uu____3273 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3273 with
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
                           | uu____3304 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3325 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3325
                         | uu____3328 ->
                             let uu____3329 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3329 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3334 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3378 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3391 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3398 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3399 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3416 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3433 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3435 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3435 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3453;
             FStar_Syntax_Syntax.vars = uu____3454;_},uu____3455)
          ->
          let uu____3476 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3476 FStar_Option.isNone
      | uu____3493 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3502 =
        let uu____3503 = FStar_Syntax_Util.un_uinst t in
        uu____3503.FStar_Syntax_Syntax.n in
      match uu____3502 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3506,uu____3507,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_3528  ->
                  match uu___115_3528 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3529 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3531 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3531 FStar_Option.isSome
      | uu____3548 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3557 = head_normal env t in
      if uu____3557
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
    let uu____3571 =
      let uu____3572 = FStar_Syntax_Syntax.null_binder t in [uu____3572] in
    let uu____3573 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3571 uu____3573 FStar_Pervasives_Native.None
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
                    let uu____3613 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3613
                | s ->
                    let uu____3618 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3618) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_3636  ->
    match uu___116_3636 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3637 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3676;
                       FStar_SMTEncoding_Term.rng = uu____3677;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3700) ->
              let uu____3709 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3720 -> false) args (FStar_List.rev xs)) in
              if uu____3709
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3724,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3728 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3732 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3732)) in
              if uu____3728
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3736 -> FStar_Pervasives_Native.None in
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
    | uu____3966 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3971 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_3975  ->
    match uu___117_3975 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____3977 =
          let uu____3984 =
            let uu____3987 =
              let uu____3988 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____3988 in
            [uu____3987] in
          ("FStar.Char.Char", uu____3984) in
        FStar_SMTEncoding_Util.mkApp uu____3977
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____4002 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____4002
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4004) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____4020) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4023 =
          let uu____4024 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____4024 in
        failwith uu____4023
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
        | FStar_Syntax_Syntax.Tm_arrow uu____4045 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4058 ->
            let uu____4065 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4065
        | uu____4066 ->
            if norm1
            then let uu____4067 = whnf env t1 in aux false uu____4067
            else
              (let uu____4069 =
                 let uu____4070 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4071 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4070 uu____4071 in
               failwith uu____4069) in
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
    | uu____4103 ->
        let uu____4104 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4104)
let is_arithmetic_primitive:
  'Auu____4121 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4121 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4141::uu____4142::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4146::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4149 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4171 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4187 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4194 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4194)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4233)::uu____4234::uu____4235::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4286)::uu____4287::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4324 -> false
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
        (let uu____4533 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4533
         then
           let uu____4534 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4534
         else ());
        (let uu____4536 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4620  ->
                   fun b  ->
                     match uu____4620 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4699 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4715 = gen_term_var env1 x in
                           match uu____4715 with
                           | (xxsym,xx,env') ->
                               let uu____4739 =
                                 let uu____4744 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4744 env1 xx in
                               (match uu____4739 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4699 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4536 with
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
          let uu____4903 = encode_term t env in
          match uu____4903 with
          | (t1,decls) ->
              let uu____4914 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4914, decls)
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
          let uu____4925 = encode_term t env in
          match uu____4925 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4940 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4940, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4942 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4942, decls))
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
        let uu____4948 = encode_args args_e env in
        match uu____4948 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4967 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4976 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4976 in
            let binary arg_tms1 =
              let uu____4989 =
                let uu____4990 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4990 in
              let uu____4991 =
                let uu____4992 =
                  let uu____4993 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4993 in
                FStar_SMTEncoding_Term.unboxInt uu____4992 in
              (uu____4989, uu____4991) in
            let mk_default uu____4999 =
              let uu____5000 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5000 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5051 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5051
              then
                let uu____5052 = let uu____5053 = mk_args ts in op uu____5053 in
                FStar_All.pipe_right uu____5052 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5082 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5082
              then
                let uu____5083 = binary ts in
                match uu____5083 with
                | (t1,t2) ->
                    let uu____5090 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5090
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5094 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5094
                 then
                   let uu____5095 = op (binary ts) in
                   FStar_All.pipe_right uu____5095
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
            let uu____5226 =
              let uu____5235 =
                FStar_List.tryFind
                  (fun uu____5257  ->
                     match uu____5257 with
                     | (l,uu____5267) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5235 FStar_Util.must in
            (match uu____5226 with
             | (uu____5306,op) ->
                 let uu____5316 = op arg_tms in (uu____5316, decls))
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
        let uu____5324 = FStar_List.hd args_e in
        match uu____5324 with
        | (tm_sz,uu____5332) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5342 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5342 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5350 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5350);
                   t_decls) in
            let uu____5351 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5371::(sz_arg,uu____5373)::uu____5374::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5423 =
                    let uu____5426 = FStar_List.tail args_e in
                    FStar_List.tail uu____5426 in
                  let uu____5429 =
                    let uu____5432 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5432 in
                  (uu____5423, uu____5429)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5438::(sz_arg,uu____5440)::uu____5441::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5490 =
                    let uu____5491 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5491 in
                  failwith uu____5490
              | uu____5500 ->
                  let uu____5507 = FStar_List.tail args_e in
                  (uu____5507, FStar_Pervasives_Native.None) in
            (match uu____5351 with
             | (arg_tms,ext_sz) ->
                 let uu____5530 = encode_args arg_tms env in
                 (match uu____5530 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5551 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5560 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5560 in
                      let unary_arith arg_tms2 =
                        let uu____5569 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5569 in
                      let binary arg_tms2 =
                        let uu____5582 =
                          let uu____5583 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5583 in
                        let uu____5584 =
                          let uu____5585 =
                            let uu____5586 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5586 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5585 in
                        (uu____5582, uu____5584) in
                      let binary_arith arg_tms2 =
                        let uu____5601 =
                          let uu____5602 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5602 in
                        let uu____5603 =
                          let uu____5604 =
                            let uu____5605 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5605 in
                          FStar_SMTEncoding_Term.unboxInt uu____5604 in
                        (uu____5601, uu____5603) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5654 =
                          let uu____5655 = mk_args ts in op uu____5655 in
                        FStar_All.pipe_right uu____5654 resBox in
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
                        let uu____5745 =
                          let uu____5748 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5748 in
                        let uu____5750 =
                          let uu____5753 =
                            let uu____5754 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5754 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5753 in
                        mk_bv uu____5745 unary uu____5750 arg_tms2 in
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
                      let uu____5929 =
                        let uu____5938 =
                          FStar_List.tryFind
                            (fun uu____5960  ->
                               match uu____5960 with
                               | (l,uu____5970) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5938 FStar_Util.must in
                      (match uu____5929 with
                       | (uu____6011,op) ->
                           let uu____6021 = op arg_tms1 in
                           (uu____6021, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6032 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6032
       then
         let uu____6033 = FStar_Syntax_Print.tag_of_term t in
         let uu____6034 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6035 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6033 uu____6034
           uu____6035
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6041 ->
           let uu____6066 =
             let uu____6067 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6068 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6069 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6070 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6067
               uu____6068 uu____6069 uu____6070 in
           failwith uu____6066
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6075 =
             let uu____6076 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6077 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6078 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6079 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6076
               uu____6077 uu____6078 uu____6079 in
           failwith uu____6075
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6085 =
             let uu____6086 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6086 in
           failwith uu____6085
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6093) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6134;
              FStar_Syntax_Syntax.vars = uu____6135;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6152 = varops.fresh "t" in
             (uu____6152, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6155 =
               let uu____6166 =
                 let uu____6169 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6169 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6166) in
             FStar_SMTEncoding_Term.DeclFun uu____6155 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6177) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6187 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6187, [])
       | FStar_Syntax_Syntax.Tm_type uu____6190 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6194) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6200 = encode_const c in (uu____6200, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6222 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6222 with
            | (binders1,res) ->
                let uu____6233 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6233
                then
                  let uu____6238 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6238 with
                   | (vars,guards,env',decls,uu____6263) ->
                       let fsym =
                         let uu____6281 = varops.fresh "f" in
                         (uu____6281, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6284 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_6293 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_6293.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_6293.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_6293.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_6293.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_6293.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_6293.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_6293.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_6293.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_6293.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_6293.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_6293.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_6293.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_6293.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_6293.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_6293.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_6293.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_6293.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_6293.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_6293.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___141_6293.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___141_6293.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___141_6293.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_6293.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_6293.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_6293.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_6293.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___141_6293.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___141_6293.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___141_6293.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___141_6293.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___141_6293.FStar_TypeChecker_Env.tc_hooks)
                            }) res in
                       (match uu____6284 with
                        | (pre_opt,res_t) ->
                            let uu____6304 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6304 with
                             | (res_pred,decls') ->
                                 let uu____6315 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6328 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6328, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6332 =
                                         encode_formula pre env' in
                                       (match uu____6332 with
                                        | (guard,decls0) ->
                                            let uu____6345 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6345, decls0)) in
                                 (match uu____6315 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6357 =
                                          let uu____6368 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6368) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6357 in
                                      let cvars =
                                        let uu____6386 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6386
                                          (FStar_List.filter
                                             (fun uu____6400  ->
                                                match uu____6400 with
                                                | (x,uu____6406) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6425 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6425 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6433 =
                                             let uu____6434 =
                                               let uu____6441 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6441) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6434 in
                                           (uu____6433,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6461 =
                                               let uu____6462 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6462 in
                                             varops.mk_unique uu____6461 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6473 =
                                               FStar_Options.log_queries () in
                                             if uu____6473
                                             then
                                               let uu____6476 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6476
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6484 =
                                               let uu____6491 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6491) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6484 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6503 =
                                               let uu____6510 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6510,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6503 in
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
                                             let uu____6531 =
                                               let uu____6538 =
                                                 let uu____6539 =
                                                   let uu____6550 =
                                                     let uu____6551 =
                                                       let uu____6556 =
                                                         let uu____6557 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6557 in
                                                       (f_has_t, uu____6556) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6551 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6550) in
                                                 mkForall_fuel uu____6539 in
                                               (uu____6538,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6531 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6580 =
                                               let uu____6587 =
                                                 let uu____6588 =
                                                   let uu____6599 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6599) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6588 in
                                               (uu____6587,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6580 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6624 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6624);
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
                     let uu____6639 =
                       let uu____6646 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6646,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6639 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6658 =
                       let uu____6665 =
                         let uu____6666 =
                           let uu____6677 =
                             let uu____6678 =
                               let uu____6683 =
                                 let uu____6684 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6684 in
                               (f_has_t, uu____6683) in
                             FStar_SMTEncoding_Util.mkImp uu____6678 in
                           ([[f_has_t]], [fsym], uu____6677) in
                         mkForall_fuel uu____6666 in
                       (uu____6665, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6658 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6711 ->
           let uu____6718 =
             let uu____6723 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6723 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6730;
                 FStar_Syntax_Syntax.vars = uu____6731;_} ->
                 let uu____6738 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6738 with
                  | (b,f1) ->
                      let uu____6763 =
                        let uu____6764 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6764 in
                      (uu____6763, f1))
             | uu____6773 -> failwith "impossible" in
           (match uu____6718 with
            | (x,f) ->
                let uu____6784 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6784 with
                 | (base_t,decls) ->
                     let uu____6795 = gen_term_var env x in
                     (match uu____6795 with
                      | (x1,xtm,env') ->
                          let uu____6809 = encode_formula f env' in
                          (match uu____6809 with
                           | (refinement,decls') ->
                               let uu____6820 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6820 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6836 =
                                        let uu____6839 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6846 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6839
                                          uu____6846 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6836 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6879  ->
                                              match uu____6879 with
                                              | (y,uu____6885) ->
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
                                    let uu____6918 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6918 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6926 =
                                           let uu____6927 =
                                             let uu____6934 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6934) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6927 in
                                         (uu____6926,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6955 =
                                             let uu____6956 =
                                               let uu____6957 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6957 in
                                             Prims.strcat module_name
                                               uu____6956 in
                                           varops.mk_unique uu____6955 in
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
                                           let uu____6971 =
                                             let uu____6978 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6978) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6971 in
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
                                           let uu____6993 =
                                             let uu____7000 =
                                               let uu____7001 =
                                                 let uu____7012 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7012) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7001 in
                                             (uu____7000,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6993 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7038 =
                                             let uu____7045 =
                                               let uu____7046 =
                                                 let uu____7057 =
                                                   let uu____7058 =
                                                     let uu____7063 =
                                                       let uu____7064 =
                                                         let uu____7075 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7075) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7064 in
                                                     (uu____7063, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7058 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7057) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7046 in
                                             (uu____7045,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7038 in
                                         let t_kinding =
                                           let uu____7113 =
                                             let uu____7120 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7120,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7113 in
                                         let t_interp =
                                           let uu____7138 =
                                             let uu____7145 =
                                               let uu____7146 =
                                                 let uu____7157 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7157) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7146 in
                                             let uu____7180 =
                                               let uu____7183 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7183 in
                                             (uu____7145, uu____7180,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7138 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7190 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7190);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7220 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7220 in
           let uu____7221 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7221 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7233 =
                    let uu____7240 =
                      let uu____7241 =
                        let uu____7242 =
                          let uu____7243 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7243 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7242 in
                      varops.mk_unique uu____7241 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7240) in
                  FStar_SMTEncoding_Util.mkAssume uu____7233 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7248 ->
           let uu____7263 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7263 with
            | (head1,args_e) ->
                let uu____7304 =
                  let uu____7317 =
                    let uu____7318 = FStar_Syntax_Subst.compress head1 in
                    uu____7318.FStar_Syntax_Syntax.n in
                  (uu____7317, args_e) in
                (match uu____7304 with
                 | uu____7333 when head_redex env head1 ->
                     let uu____7346 = whnf env t in
                     encode_term uu____7346 env
                 | uu____7347 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7366 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7380;
                       FStar_Syntax_Syntax.vars = uu____7381;_},uu____7382),uu____7383::
                    (v1,uu____7385)::(v2,uu____7387)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7438 = encode_term v1 env in
                     (match uu____7438 with
                      | (v11,decls1) ->
                          let uu____7449 = encode_term v2 env in
                          (match uu____7449 with
                           | (v21,decls2) ->
                               let uu____7460 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7460,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7464::(v1,uu____7466)::(v2,uu____7468)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7515 = encode_term v1 env in
                     (match uu____7515 with
                      | (v11,decls1) ->
                          let uu____7526 = encode_term v2 env in
                          (match uu____7526 with
                           | (v21,decls2) ->
                               let uu____7537 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7537,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7540) ->
                     let e0 =
                       let uu____7558 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7558 in
                     ((let uu____7566 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7566
                       then
                         let uu____7567 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7567
                       else ());
                      (let e =
                         let uu____7572 =
                           let uu____7573 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7574 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7573
                             uu____7574 in
                         uu____7572 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7583),(arg,uu____7585)::[]) -> encode_term arg env
                 | uu____7610 ->
                     let uu____7623 = encode_args args_e env in
                     (match uu____7623 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7678 = encode_term head1 env in
                            match uu____7678 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7742 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7742 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7820  ->
                                                 fun uu____7821  ->
                                                   match (uu____7820,
                                                           uu____7821)
                                                   with
                                                   | ((bv,uu____7843),
                                                      (a,uu____7845)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7863 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7863
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7868 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7868 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7883 =
                                                   let uu____7890 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7899 =
                                                     let uu____7900 =
                                                       let uu____7901 =
                                                         let uu____7902 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7902 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7901 in
                                                     varops.mk_unique
                                                       uu____7900 in
                                                   (uu____7890,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7899) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7883 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7919 = lookup_free_var_sym env fv in
                            match uu____7919 with
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
                                   FStar_Syntax_Syntax.pos = uu____7950;
                                   FStar_Syntax_Syntax.vars = uu____7951;_},uu____7952)
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
                                   FStar_Syntax_Syntax.pos = uu____7963;
                                   FStar_Syntax_Syntax.vars = uu____7964;_},uu____7965)
                                ->
                                let uu____7970 =
                                  let uu____7971 =
                                    let uu____7976 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7976
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7971
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7970
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8006 =
                                  let uu____8007 =
                                    let uu____8012 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8012
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8007
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8006
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8041,(FStar_Util.Inl t1,uu____8043),uu____8044)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8093,(FStar_Util.Inr c,uu____8095),uu____8096)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8145 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8172 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8172 in
                               let uu____8173 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8173 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8189;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8190;_},uu____8191)
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
                                     | uu____8205 ->
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
           let uu____8254 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8254 with
            | (bs1,body1,opening) ->
                let fallback uu____8277 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8284 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8284, [decl]) in
                let is_impure rc =
                  let uu____8291 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8291 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8301 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8301
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8321 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8321
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8325 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8325)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8332 =
                         let uu____8333 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8333 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8332);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8335 =
                       (is_impure rc) &&
                         (let uu____8337 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8337) in
                     if uu____8335
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8344 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8344 with
                        | (vars,guards,envbody,decls,uu____8369) ->
                            let body2 =
                              let uu____8383 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8383
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8385 = encode_term body2 envbody in
                            (match uu____8385 with
                             | (body3,decls') ->
                                 let uu____8396 =
                                   let uu____8405 = codomain_eff rc in
                                   match uu____8405 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8424 = encode_term tfun env in
                                       (match uu____8424 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8396 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8456 =
                                          let uu____8467 =
                                            let uu____8468 =
                                              let uu____8473 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8473, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8468 in
                                          ([], vars, uu____8467) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8456 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8485 =
                                              let uu____8488 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8488
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8485 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8507 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8507 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8515 =
                                             let uu____8516 =
                                               let uu____8523 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8523) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8516 in
                                           (uu____8515,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8534 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8534 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8545 =
                                                    let uu____8546 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8546 = cache_size in
                                                  if uu____8545
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
                                                    let uu____8562 =
                                                      let uu____8563 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8563 in
                                                    varops.mk_unique
                                                      uu____8562 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8570 =
                                                    let uu____8577 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8577) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8570 in
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
                                                      let uu____8595 =
                                                        let uu____8596 =
                                                          let uu____8603 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8603,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8596 in
                                                      [uu____8595] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8616 =
                                                    let uu____8623 =
                                                      let uu____8624 =
                                                        let uu____8635 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8635) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8624 in
                                                    (uu____8623,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8616 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8652 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8652);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8655,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8656;
                          FStar_Syntax_Syntax.lbunivs = uu____8657;
                          FStar_Syntax_Syntax.lbtyp = uu____8658;
                          FStar_Syntax_Syntax.lbeff = uu____8659;
                          FStar_Syntax_Syntax.lbdef = uu____8660;_}::uu____8661),uu____8662)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8688;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8690;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8711 ->
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
              let uu____8781 = encode_term e1 env in
              match uu____8781 with
              | (ee1,decls1) ->
                  let uu____8792 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8792 with
                   | (xs,e21) ->
                       let uu____8817 = FStar_List.hd xs in
                       (match uu____8817 with
                        | (x1,uu____8831) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8833 = encode_body e21 env' in
                            (match uu____8833 with
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
            let uu____8865 =
              let uu____8872 =
                let uu____8873 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8873 in
              gen_term_var env uu____8872 in
            match uu____8865 with
            | (scrsym,scr',env1) ->
                let uu____8881 = encode_term e env1 in
                (match uu____8881 with
                 | (scr,decls) ->
                     let uu____8892 =
                       let encode_branch b uu____8917 =
                         match uu____8917 with
                         | (else_case,decls1) ->
                             let uu____8936 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8936 with
                              | (p,w,br) ->
                                  let uu____8962 = encode_pat env1 p in
                                  (match uu____8962 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8999  ->
                                                   match uu____8999 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9006 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9028 =
                                               encode_term w1 env2 in
                                             (match uu____9028 with
                                              | (w2,decls2) ->
                                                  let uu____9041 =
                                                    let uu____9042 =
                                                      let uu____9047 =
                                                        let uu____9048 =
                                                          let uu____9053 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9053) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9048 in
                                                      (guard, uu____9047) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9042 in
                                                  (uu____9041, decls2)) in
                                       (match uu____9006 with
                                        | (guard1,decls2) ->
                                            let uu____9066 =
                                              encode_br br env2 in
                                            (match uu____9066 with
                                             | (br1,decls3) ->
                                                 let uu____9079 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9079,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8892 with
                      | (match_tm,decls1) ->
                          let uu____9098 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9098, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9138 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9138
       then
         let uu____9139 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9139
       else ());
      (let uu____9141 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9141 with
       | (vars,pat_term) ->
           let uu____9158 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9211  ->
                     fun v1  ->
                       match uu____9211 with
                       | (env1,vars1) ->
                           let uu____9263 = gen_term_var env1 v1 in
                           (match uu____9263 with
                            | (xx,uu____9285,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9158 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9364 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9365 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9366 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9374 =
                        let uu____9379 = encode_const c in
                        (scrutinee, uu____9379) in
                      FStar_SMTEncoding_Util.mkEq uu____9374
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9400 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9400 with
                        | (uu____9407,uu____9408::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9411 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9444  ->
                                  match uu____9444 with
                                  | (arg,uu____9452) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9458 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9458)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9485) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9516 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9539 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9583  ->
                                  match uu____9583 with
                                  | (arg,uu____9597) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9603 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9603)) in
                      FStar_All.pipe_right uu____9539 FStar_List.flatten in
                let pat_term1 uu____9631 = encode_term pat_term env1 in
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
      let uu____9641 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9679  ->
                fun uu____9680  ->
                  match (uu____9679, uu____9680) with
                  | ((tms,decls),(t,uu____9716)) ->
                      let uu____9737 = encode_term t env in
                      (match uu____9737 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9641 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9794 = FStar_Syntax_Util.list_elements e in
        match uu____9794 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9815 =
          let uu____9830 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9830 FStar_Syntax_Util.head_and_args in
        match uu____9815 with
        | (head1,args) ->
            let uu____9869 =
              let uu____9882 =
                let uu____9883 = FStar_Syntax_Util.un_uinst head1 in
                uu____9883.FStar_Syntax_Syntax.n in
              (uu____9882, args) in
            (match uu____9869 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9897,uu____9898)::(e,uu____9900)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9935 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9971 =
            let uu____9986 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9986 FStar_Syntax_Util.head_and_args in
          match uu____9971 with
          | (head1,args) ->
              let uu____10027 =
                let uu____10040 =
                  let uu____10041 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10041.FStar_Syntax_Syntax.n in
                (uu____10040, args) in
              (match uu____10027 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10058)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10085 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10107 = smt_pat_or1 t1 in
            (match uu____10107 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10123 = list_elements1 e in
                 FStar_All.pipe_right uu____10123
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10141 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10141
                           (FStar_List.map one_pat)))
             | uu____10152 ->
                 let uu____10157 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10157])
        | uu____10178 ->
            let uu____10181 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10181] in
      let uu____10202 =
        let uu____10221 =
          let uu____10222 = FStar_Syntax_Subst.compress t in
          uu____10222.FStar_Syntax_Syntax.n in
        match uu____10221 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10261 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10261 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10304;
                        FStar_Syntax_Syntax.effect_name = uu____10305;
                        FStar_Syntax_Syntax.result_typ = uu____10306;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10308)::(post,uu____10310)::(pats,uu____10312)::[];
                        FStar_Syntax_Syntax.flags = uu____10313;_}
                      ->
                      let uu____10354 = lemma_pats pats in
                      (binders1, pre, post, uu____10354)
                  | uu____10371 -> failwith "impos"))
        | uu____10390 -> failwith "Impos" in
      match uu____10202 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___142_10438 = env in
            {
              bindings = (uu___142_10438.bindings);
              depth = (uu___142_10438.depth);
              tcenv = (uu___142_10438.tcenv);
              warn = (uu___142_10438.warn);
              cache = (uu___142_10438.cache);
              nolabels = (uu___142_10438.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___142_10438.encode_non_total_function_typ);
              current_module_name = (uu___142_10438.current_module_name)
            } in
          let uu____10439 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10439 with
           | (vars,guards,env2,decls,uu____10464) ->
               let uu____10477 =
                 let uu____10490 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10534 =
                             let uu____10543 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10543
                               FStar_List.unzip in
                           match uu____10534 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10490 FStar_List.unzip in
               (match uu____10477 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___143_10652 = env2 in
                      {
                        bindings = (uu___143_10652.bindings);
                        depth = (uu___143_10652.depth);
                        tcenv = (uu___143_10652.tcenv);
                        warn = (uu___143_10652.warn);
                        cache = (uu___143_10652.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___143_10652.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___143_10652.encode_non_total_function_typ);
                        current_module_name =
                          (uu___143_10652.current_module_name)
                      } in
                    let uu____10653 =
                      let uu____10658 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10658 env3 in
                    (match uu____10653 with
                     | (pre1,decls'') ->
                         let uu____10665 =
                           let uu____10670 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10670 env3 in
                         (match uu____10665 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10680 =
                                let uu____10681 =
                                  let uu____10692 =
                                    let uu____10693 =
                                      let uu____10698 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10698, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10693 in
                                  (pats, vars, uu____10692) in
                                FStar_SMTEncoding_Util.mkForall uu____10681 in
                              (uu____10680, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10717 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10717
        then
          let uu____10718 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10719 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10718 uu____10719
        else () in
      let enc f r l =
        let uu____10752 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10780 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10780 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10752 with
        | (decls,args) ->
            let uu____10809 =
              let uu___144_10810 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_10810.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_10810.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10809, decls) in
      let const_op f r uu____10841 =
        let uu____10854 = f r in (uu____10854, []) in
      let un_op f l =
        let uu____10873 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10873 in
      let bin_op f uu___118_10889 =
        match uu___118_10889 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10900 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10934 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10957  ->
                 match uu____10957 with
                 | (t,uu____10971) ->
                     let uu____10972 = encode_formula t env in
                     (match uu____10972 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10934 with
        | (decls,phis) ->
            let uu____11001 =
              let uu___145_11002 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_11002.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_11002.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11001, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11063  ->
               match uu____11063 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11082) -> false
                    | uu____11083 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11098 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11098
        else
          (let uu____11112 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11112 r rf) in
      let mk_imp1 r uu___119_11137 =
        match uu___119_11137 with
        | (lhs,uu____11143)::(rhs,uu____11145)::[] ->
            let uu____11172 = encode_formula rhs env in
            (match uu____11172 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11187) ->
                      (l1, decls1)
                  | uu____11192 ->
                      let uu____11193 = encode_formula lhs env in
                      (match uu____11193 with
                       | (l2,decls2) ->
                           let uu____11204 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11204, (FStar_List.append decls1 decls2)))))
        | uu____11207 -> failwith "impossible" in
      let mk_ite r uu___120_11228 =
        match uu___120_11228 with
        | (guard,uu____11234)::(_then,uu____11236)::(_else,uu____11238)::[]
            ->
            let uu____11275 = encode_formula guard env in
            (match uu____11275 with
             | (g,decls1) ->
                 let uu____11286 = encode_formula _then env in
                 (match uu____11286 with
                  | (t,decls2) ->
                      let uu____11297 = encode_formula _else env in
                      (match uu____11297 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11311 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11336 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11336 in
      let connectives =
        let uu____11354 =
          let uu____11367 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11367) in
        let uu____11384 =
          let uu____11399 =
            let uu____11412 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11412) in
          let uu____11429 =
            let uu____11444 =
              let uu____11459 =
                let uu____11472 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11472) in
              let uu____11489 =
                let uu____11504 =
                  let uu____11519 =
                    let uu____11532 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11532) in
                  [uu____11519;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11504 in
              uu____11459 :: uu____11489 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11444 in
          uu____11399 :: uu____11429 in
        uu____11354 :: uu____11384 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11853 = encode_formula phi' env in
            (match uu____11853 with
             | (phi2,decls) ->
                 let uu____11864 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11864, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11865 ->
            let uu____11872 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11872 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11911 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11911 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11923;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11925;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11946 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11946 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11993::(x,uu____11995)::(t,uu____11997)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12044 = encode_term x env in
                 (match uu____12044 with
                  | (x1,decls) ->
                      let uu____12055 = encode_term t env in
                      (match uu____12055 with
                       | (t1,decls') ->
                           let uu____12066 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12066, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12071)::(msg,uu____12073)::(phi2,uu____12075)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12120 =
                   let uu____12125 =
                     let uu____12126 = FStar_Syntax_Subst.compress r in
                     uu____12126.FStar_Syntax_Syntax.n in
                   let uu____12129 =
                     let uu____12130 = FStar_Syntax_Subst.compress msg in
                     uu____12130.FStar_Syntax_Syntax.n in
                   (uu____12125, uu____12129) in
                 (match uu____12120 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12139))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12145 -> fallback phi2)
             | uu____12150 when head_redex env head2 ->
                 let uu____12163 = whnf env phi1 in
                 encode_formula uu____12163 env
             | uu____12164 ->
                 let uu____12177 = encode_term phi1 env in
                 (match uu____12177 with
                  | (tt,decls) ->
                      let uu____12188 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___146_12191 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___146_12191.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___146_12191.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12188, decls)))
        | uu____12192 ->
            let uu____12193 = encode_term phi1 env in
            (match uu____12193 with
             | (tt,decls) ->
                 let uu____12204 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___147_12207 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___147_12207.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___147_12207.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12204, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12243 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12243 with
        | (vars,guards,env2,decls,uu____12282) ->
            let uu____12295 =
              let uu____12308 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12356 =
                          let uu____12365 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12395  ->
                                    match uu____12395 with
                                    | (t,uu____12405) ->
                                        encode_term t
                                          (let uu___148_12407 = env2 in
                                           {
                                             bindings =
                                               (uu___148_12407.bindings);
                                             depth = (uu___148_12407.depth);
                                             tcenv = (uu___148_12407.tcenv);
                                             warn = (uu___148_12407.warn);
                                             cache = (uu___148_12407.cache);
                                             nolabels =
                                               (uu___148_12407.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___148_12407.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___148_12407.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12365 FStar_List.unzip in
                        match uu____12356 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12308 FStar_List.unzip in
            (match uu____12295 with
             | (pats,decls') ->
                 let uu____12506 = encode_formula body env2 in
                 (match uu____12506 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12538;
                             FStar_SMTEncoding_Term.rng = uu____12539;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12554 -> guards in
                      let uu____12559 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12559, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12619  ->
                   match uu____12619 with
                   | (x,uu____12625) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12633 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12645 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12645) uu____12633 tl1 in
             let uu____12648 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12675  ->
                       match uu____12675 with
                       | (b,uu____12681) ->
                           let uu____12682 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12682)) in
             (match uu____12648 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12688) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12702 =
                    let uu____12703 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12703 in
                  FStar_Errors.warn pos uu____12702) in
       let uu____12704 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12704 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12713 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12771  ->
                     match uu____12771 with
                     | (l,uu____12785) -> FStar_Ident.lid_equals op l)) in
           (match uu____12713 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12818,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12858 = encode_q_body env vars pats body in
             match uu____12858 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12903 =
                     let uu____12914 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12914) in
                   FStar_SMTEncoding_Term.mkForall uu____12903
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12933 = encode_q_body env vars pats body in
             match uu____12933 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12977 =
                   let uu____12978 =
                     let uu____12989 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12989) in
                   FStar_SMTEncoding_Term.mkExists uu____12978
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12977, decls))))
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
  let uu____13087 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13087 with
  | (asym,a) ->
      let uu____13094 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13094 with
       | (xsym,x) ->
           let uu____13101 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13101 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13145 =
                      let uu____13156 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13156, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13145 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13182 =
                      let uu____13189 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13189) in
                    FStar_SMTEncoding_Util.mkApp uu____13182 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13202 =
                    let uu____13205 =
                      let uu____13208 =
                        let uu____13211 =
                          let uu____13212 =
                            let uu____13219 =
                              let uu____13220 =
                                let uu____13231 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13231) in
                              FStar_SMTEncoding_Util.mkForall uu____13220 in
                            (uu____13219, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13212 in
                        let uu____13248 =
                          let uu____13251 =
                            let uu____13252 =
                              let uu____13259 =
                                let uu____13260 =
                                  let uu____13271 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13271) in
                                FStar_SMTEncoding_Util.mkForall uu____13260 in
                              (uu____13259,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13252 in
                          [uu____13251] in
                        uu____13211 :: uu____13248 in
                      xtok_decl :: uu____13208 in
                    xname_decl :: uu____13205 in
                  (xtok1, uu____13202) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13362 =
                    let uu____13375 =
                      let uu____13384 =
                        let uu____13385 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13385 in
                      quant axy uu____13384 in
                    (FStar_Parser_Const.op_Eq, uu____13375) in
                  let uu____13394 =
                    let uu____13409 =
                      let uu____13422 =
                        let uu____13431 =
                          let uu____13432 =
                            let uu____13433 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13433 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13432 in
                        quant axy uu____13431 in
                      (FStar_Parser_Const.op_notEq, uu____13422) in
                    let uu____13442 =
                      let uu____13457 =
                        let uu____13470 =
                          let uu____13479 =
                            let uu____13480 =
                              let uu____13481 =
                                let uu____13486 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13487 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13486, uu____13487) in
                              FStar_SMTEncoding_Util.mkLT uu____13481 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13480 in
                          quant xy uu____13479 in
                        (FStar_Parser_Const.op_LT, uu____13470) in
                      let uu____13496 =
                        let uu____13511 =
                          let uu____13524 =
                            let uu____13533 =
                              let uu____13534 =
                                let uu____13535 =
                                  let uu____13540 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13541 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13540, uu____13541) in
                                FStar_SMTEncoding_Util.mkLTE uu____13535 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13534 in
                            quant xy uu____13533 in
                          (FStar_Parser_Const.op_LTE, uu____13524) in
                        let uu____13550 =
                          let uu____13565 =
                            let uu____13578 =
                              let uu____13587 =
                                let uu____13588 =
                                  let uu____13589 =
                                    let uu____13594 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13595 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13594, uu____13595) in
                                  FStar_SMTEncoding_Util.mkGT uu____13589 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13588 in
                              quant xy uu____13587 in
                            (FStar_Parser_Const.op_GT, uu____13578) in
                          let uu____13604 =
                            let uu____13619 =
                              let uu____13632 =
                                let uu____13641 =
                                  let uu____13642 =
                                    let uu____13643 =
                                      let uu____13648 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13649 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13648, uu____13649) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13643 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13642 in
                                quant xy uu____13641 in
                              (FStar_Parser_Const.op_GTE, uu____13632) in
                            let uu____13658 =
                              let uu____13673 =
                                let uu____13686 =
                                  let uu____13695 =
                                    let uu____13696 =
                                      let uu____13697 =
                                        let uu____13702 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13703 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13702, uu____13703) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13697 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13696 in
                                  quant xy uu____13695 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13686) in
                              let uu____13712 =
                                let uu____13727 =
                                  let uu____13740 =
                                    let uu____13749 =
                                      let uu____13750 =
                                        let uu____13751 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13751 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13750 in
                                    quant qx uu____13749 in
                                  (FStar_Parser_Const.op_Minus, uu____13740) in
                                let uu____13760 =
                                  let uu____13775 =
                                    let uu____13788 =
                                      let uu____13797 =
                                        let uu____13798 =
                                          let uu____13799 =
                                            let uu____13804 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13805 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13804, uu____13805) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13799 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13798 in
                                      quant xy uu____13797 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13788) in
                                  let uu____13814 =
                                    let uu____13829 =
                                      let uu____13842 =
                                        let uu____13851 =
                                          let uu____13852 =
                                            let uu____13853 =
                                              let uu____13858 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13859 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13858, uu____13859) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13853 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13852 in
                                        quant xy uu____13851 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13842) in
                                    let uu____13868 =
                                      let uu____13883 =
                                        let uu____13896 =
                                          let uu____13905 =
                                            let uu____13906 =
                                              let uu____13907 =
                                                let uu____13912 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13913 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13912, uu____13913) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13907 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13906 in
                                          quant xy uu____13905 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13896) in
                                      let uu____13922 =
                                        let uu____13937 =
                                          let uu____13950 =
                                            let uu____13959 =
                                              let uu____13960 =
                                                let uu____13961 =
                                                  let uu____13966 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13967 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13966, uu____13967) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13961 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13960 in
                                            quant xy uu____13959 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13950) in
                                        let uu____13976 =
                                          let uu____13991 =
                                            let uu____14004 =
                                              let uu____14013 =
                                                let uu____14014 =
                                                  let uu____14015 =
                                                    let uu____14020 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14021 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14020,
                                                      uu____14021) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14015 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14014 in
                                              quant xy uu____14013 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14004) in
                                          let uu____14030 =
                                            let uu____14045 =
                                              let uu____14058 =
                                                let uu____14067 =
                                                  let uu____14068 =
                                                    let uu____14069 =
                                                      let uu____14074 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14075 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14074,
                                                        uu____14075) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14069 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14068 in
                                                quant xy uu____14067 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14058) in
                                            let uu____14084 =
                                              let uu____14099 =
                                                let uu____14112 =
                                                  let uu____14121 =
                                                    let uu____14122 =
                                                      let uu____14123 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14123 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14122 in
                                                  quant qx uu____14121 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14112) in
                                              [uu____14099] in
                                            uu____14045 :: uu____14084 in
                                          uu____13991 :: uu____14030 in
                                        uu____13937 :: uu____13976 in
                                      uu____13883 :: uu____13922 in
                                    uu____13829 :: uu____13868 in
                                  uu____13775 :: uu____13814 in
                                uu____13727 :: uu____13760 in
                              uu____13673 :: uu____13712 in
                            uu____13619 :: uu____13658 in
                          uu____13565 :: uu____13604 in
                        uu____13511 :: uu____13550 in
                      uu____13457 :: uu____13496 in
                    uu____13409 :: uu____13442 in
                  uu____13362 :: uu____13394 in
                let mk1 l v1 =
                  let uu____14337 =
                    let uu____14346 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14404  ->
                              match uu____14404 with
                              | (l',uu____14418) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14346
                      (FStar_Option.map
                         (fun uu____14478  ->
                            match uu____14478 with | (uu____14497,b) -> b v1)) in
                  FStar_All.pipe_right uu____14337 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14568  ->
                          match uu____14568 with
                          | (l',uu____14582) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14623 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14623 with
        | (xxsym,xx) ->
            let uu____14630 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14630 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14640 =
                   let uu____14647 =
                     let uu____14648 =
                       let uu____14659 =
                         let uu____14660 =
                           let uu____14665 =
                             let uu____14666 =
                               let uu____14671 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14671) in
                             FStar_SMTEncoding_Util.mkEq uu____14666 in
                           (xx_has_type, uu____14665) in
                         FStar_SMTEncoding_Util.mkImp uu____14660 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14659) in
                     FStar_SMTEncoding_Util.mkForall uu____14648 in
                   let uu____14696 =
                     let uu____14697 =
                       let uu____14698 =
                         let uu____14699 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14699 in
                       Prims.strcat module_name uu____14698 in
                     varops.mk_unique uu____14697 in
                   (uu____14647, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14696) in
                 FStar_SMTEncoding_Util.mkAssume uu____14640)
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
    let uu____14739 =
      let uu____14740 =
        let uu____14747 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14747, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14740 in
    let uu____14750 =
      let uu____14753 =
        let uu____14754 =
          let uu____14761 =
            let uu____14762 =
              let uu____14773 =
                let uu____14774 =
                  let uu____14779 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14779) in
                FStar_SMTEncoding_Util.mkImp uu____14774 in
              ([[typing_pred]], [xx], uu____14773) in
            mkForall_fuel uu____14762 in
          (uu____14761, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14754 in
      [uu____14753] in
    uu____14739 :: uu____14750 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14821 =
      let uu____14822 =
        let uu____14829 =
          let uu____14830 =
            let uu____14841 =
              let uu____14846 =
                let uu____14849 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14849] in
              [uu____14846] in
            let uu____14854 =
              let uu____14855 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14855 tt in
            (uu____14841, [bb], uu____14854) in
          FStar_SMTEncoding_Util.mkForall uu____14830 in
        (uu____14829, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14822 in
    let uu____14876 =
      let uu____14879 =
        let uu____14880 =
          let uu____14887 =
            let uu____14888 =
              let uu____14899 =
                let uu____14900 =
                  let uu____14905 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14905) in
                FStar_SMTEncoding_Util.mkImp uu____14900 in
              ([[typing_pred]], [xx], uu____14899) in
            mkForall_fuel uu____14888 in
          (uu____14887, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14880 in
      [uu____14879] in
    uu____14821 :: uu____14876 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14955 =
        let uu____14956 =
          let uu____14963 =
            let uu____14966 =
              let uu____14969 =
                let uu____14972 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14973 =
                  let uu____14976 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14976] in
                uu____14972 :: uu____14973 in
              tt :: uu____14969 in
            tt :: uu____14966 in
          ("Prims.Precedes", uu____14963) in
        FStar_SMTEncoding_Util.mkApp uu____14956 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14955 in
    let precedes_y_x =
      let uu____14980 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14980 in
    let uu____14983 =
      let uu____14984 =
        let uu____14991 =
          let uu____14992 =
            let uu____15003 =
              let uu____15008 =
                let uu____15011 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15011] in
              [uu____15008] in
            let uu____15016 =
              let uu____15017 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15017 tt in
            (uu____15003, [bb], uu____15016) in
          FStar_SMTEncoding_Util.mkForall uu____14992 in
        (uu____14991, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14984 in
    let uu____15038 =
      let uu____15041 =
        let uu____15042 =
          let uu____15049 =
            let uu____15050 =
              let uu____15061 =
                let uu____15062 =
                  let uu____15067 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15067) in
                FStar_SMTEncoding_Util.mkImp uu____15062 in
              ([[typing_pred]], [xx], uu____15061) in
            mkForall_fuel uu____15050 in
          (uu____15049, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15042 in
      let uu____15092 =
        let uu____15095 =
          let uu____15096 =
            let uu____15103 =
              let uu____15104 =
                let uu____15115 =
                  let uu____15116 =
                    let uu____15121 =
                      let uu____15122 =
                        let uu____15125 =
                          let uu____15128 =
                            let uu____15131 =
                              let uu____15132 =
                                let uu____15137 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15138 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15137, uu____15138) in
                              FStar_SMTEncoding_Util.mkGT uu____15132 in
                            let uu____15139 =
                              let uu____15142 =
                                let uu____15143 =
                                  let uu____15148 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15149 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15148, uu____15149) in
                                FStar_SMTEncoding_Util.mkGTE uu____15143 in
                              let uu____15150 =
                                let uu____15153 =
                                  let uu____15154 =
                                    let uu____15159 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15160 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15159, uu____15160) in
                                  FStar_SMTEncoding_Util.mkLT uu____15154 in
                                [uu____15153] in
                              uu____15142 :: uu____15150 in
                            uu____15131 :: uu____15139 in
                          typing_pred_y :: uu____15128 in
                        typing_pred :: uu____15125 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15122 in
                    (uu____15121, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15116 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15115) in
              mkForall_fuel uu____15104 in
            (uu____15103,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15096 in
        [uu____15095] in
      uu____15041 :: uu____15092 in
    uu____14983 :: uu____15038 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15206 =
      let uu____15207 =
        let uu____15214 =
          let uu____15215 =
            let uu____15226 =
              let uu____15231 =
                let uu____15234 = FStar_SMTEncoding_Term.boxString b in
                [uu____15234] in
              [uu____15231] in
            let uu____15239 =
              let uu____15240 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15240 tt in
            (uu____15226, [bb], uu____15239) in
          FStar_SMTEncoding_Util.mkForall uu____15215 in
        (uu____15214, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15207 in
    let uu____15261 =
      let uu____15264 =
        let uu____15265 =
          let uu____15272 =
            let uu____15273 =
              let uu____15284 =
                let uu____15285 =
                  let uu____15290 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15290) in
                FStar_SMTEncoding_Util.mkImp uu____15285 in
              ([[typing_pred]], [xx], uu____15284) in
            mkForall_fuel uu____15273 in
          (uu____15272, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15265 in
      [uu____15264] in
    uu____15206 :: uu____15261 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15343 =
      let uu____15344 =
        let uu____15351 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15351, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15344 in
    [uu____15343] in
  let mk_and_interp env conj uu____15363 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15388 =
      let uu____15389 =
        let uu____15396 =
          let uu____15397 =
            let uu____15408 =
              let uu____15409 =
                let uu____15414 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15414, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15409 in
            ([[l_and_a_b]], [aa; bb], uu____15408) in
          FStar_SMTEncoding_Util.mkForall uu____15397 in
        (uu____15396, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15389 in
    [uu____15388] in
  let mk_or_interp env disj uu____15452 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15477 =
      let uu____15478 =
        let uu____15485 =
          let uu____15486 =
            let uu____15497 =
              let uu____15498 =
                let uu____15503 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15503, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15498 in
            ([[l_or_a_b]], [aa; bb], uu____15497) in
          FStar_SMTEncoding_Util.mkForall uu____15486 in
        (uu____15485, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15478 in
    [uu____15477] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15566 =
      let uu____15567 =
        let uu____15574 =
          let uu____15575 =
            let uu____15586 =
              let uu____15587 =
                let uu____15592 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15592, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15587 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15586) in
          FStar_SMTEncoding_Util.mkForall uu____15575 in
        (uu____15574, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15567 in
    [uu____15566] in
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
    let uu____15665 =
      let uu____15666 =
        let uu____15673 =
          let uu____15674 =
            let uu____15685 =
              let uu____15686 =
                let uu____15691 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15691, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15686 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15685) in
          FStar_SMTEncoding_Util.mkForall uu____15674 in
        (uu____15673, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15666 in
    [uu____15665] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15762 =
      let uu____15763 =
        let uu____15770 =
          let uu____15771 =
            let uu____15782 =
              let uu____15783 =
                let uu____15788 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15788, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15783 in
            ([[l_imp_a_b]], [aa; bb], uu____15782) in
          FStar_SMTEncoding_Util.mkForall uu____15771 in
        (uu____15770, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15763 in
    [uu____15762] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15851 =
      let uu____15852 =
        let uu____15859 =
          let uu____15860 =
            let uu____15871 =
              let uu____15872 =
                let uu____15877 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15877, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15872 in
            ([[l_iff_a_b]], [aa; bb], uu____15871) in
          FStar_SMTEncoding_Util.mkForall uu____15860 in
        (uu____15859, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15852 in
    [uu____15851] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15929 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15929 in
    let uu____15932 =
      let uu____15933 =
        let uu____15940 =
          let uu____15941 =
            let uu____15952 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15952) in
          FStar_SMTEncoding_Util.mkForall uu____15941 in
        (uu____15940, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15933 in
    [uu____15932] in
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
      let uu____16012 =
        let uu____16019 =
          let uu____16022 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16022] in
        ("Valid", uu____16019) in
      FStar_SMTEncoding_Util.mkApp uu____16012 in
    let uu____16025 =
      let uu____16026 =
        let uu____16033 =
          let uu____16034 =
            let uu____16045 =
              let uu____16046 =
                let uu____16051 =
                  let uu____16052 =
                    let uu____16063 =
                      let uu____16068 =
                        let uu____16071 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16071] in
                      [uu____16068] in
                    let uu____16076 =
                      let uu____16077 =
                        let uu____16082 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16082, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16077 in
                    (uu____16063, [xx1], uu____16076) in
                  FStar_SMTEncoding_Util.mkForall uu____16052 in
                (uu____16051, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16046 in
            ([[l_forall_a_b]], [aa; bb], uu____16045) in
          FStar_SMTEncoding_Util.mkForall uu____16034 in
        (uu____16033, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16026 in
    [uu____16025] in
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
      let uu____16164 =
        let uu____16171 =
          let uu____16174 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16174] in
        ("Valid", uu____16171) in
      FStar_SMTEncoding_Util.mkApp uu____16164 in
    let uu____16177 =
      let uu____16178 =
        let uu____16185 =
          let uu____16186 =
            let uu____16197 =
              let uu____16198 =
                let uu____16203 =
                  let uu____16204 =
                    let uu____16215 =
                      let uu____16220 =
                        let uu____16223 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16223] in
                      [uu____16220] in
                    let uu____16228 =
                      let uu____16229 =
                        let uu____16234 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16234, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16229 in
                    (uu____16215, [xx1], uu____16228) in
                  FStar_SMTEncoding_Util.mkExists uu____16204 in
                (uu____16203, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16198 in
            ([[l_exists_a_b]], [aa; bb], uu____16197) in
          FStar_SMTEncoding_Util.mkForall uu____16186 in
        (uu____16185, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16178 in
    [uu____16177] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16294 =
      let uu____16295 =
        let uu____16302 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16303 = varops.mk_unique "typing_range_const" in
        (uu____16302, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16303) in
      FStar_SMTEncoding_Util.mkAssume uu____16295 in
    [uu____16294] in
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
        let uu____16337 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16337 x1 t in
      let uu____16338 =
        let uu____16349 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16349) in
      FStar_SMTEncoding_Util.mkForall uu____16338 in
    let uu____16372 =
      let uu____16373 =
        let uu____16380 =
          let uu____16381 =
            let uu____16392 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16392) in
          FStar_SMTEncoding_Util.mkForall uu____16381 in
        (uu____16380,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16373 in
    [uu____16372] in
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
          let uu____16716 =
            FStar_Util.find_opt
              (fun uu____16742  ->
                 match uu____16742 with
                 | (l,uu____16754) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16716 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16779,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16818 = encode_function_type_as_formula t env in
        match uu____16818 with
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
              let uu____16864 =
                ((let uu____16867 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16867) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16864
              then
                let uu____16874 = new_term_constant_and_tok_from_lid env lid in
                match uu____16874 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16893 =
                        let uu____16894 = FStar_Syntax_Subst.compress t_norm in
                        uu____16894.FStar_Syntax_Syntax.n in
                      match uu____16893 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16900) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16930  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16935 -> [] in
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
                (let uu____16949 = prims.is lid in
                 if uu____16949
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16957 = prims.mk lid vname in
                   match uu____16957 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16981 =
                      let uu____16992 = curried_arrow_formals_comp t_norm in
                      match uu____16992 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17010 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17010
                            then
                              let uu____17011 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___149_17014 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___149_17014.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___149_17014.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___149_17014.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___149_17014.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___149_17014.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___149_17014.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___149_17014.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___149_17014.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___149_17014.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___149_17014.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___149_17014.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___149_17014.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___149_17014.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___149_17014.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___149_17014.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___149_17014.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___149_17014.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___149_17014.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___149_17014.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___149_17014.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___149_17014.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___149_17014.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___149_17014.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___149_17014.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___149_17014.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___149_17014.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___149_17014.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___149_17014.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___149_17014.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___149_17014.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___149_17014.FStar_TypeChecker_Env.tc_hooks)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17011
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17026 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17026)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16981 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17071 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17071 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17092 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___121_17134  ->
                                       match uu___121_17134 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17138 =
                                             FStar_Util.prefix vars in
                                           (match uu____17138 with
                                            | (uu____17159,(xxsym,uu____17161))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17179 =
                                                  let uu____17180 =
                                                    let uu____17187 =
                                                      let uu____17188 =
                                                        let uu____17199 =
                                                          let uu____17200 =
                                                            let uu____17205 =
                                                              let uu____17206
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17206 in
                                                            (vapp,
                                                              uu____17205) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17200 in
                                                        ([[vapp]], vars,
                                                          uu____17199) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17188 in
                                                    (uu____17187,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17180 in
                                                [uu____17179])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17225 =
                                             FStar_Util.prefix vars in
                                           (match uu____17225 with
                                            | (uu____17246,(xxsym,uu____17248))
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
                                                let uu____17271 =
                                                  let uu____17272 =
                                                    let uu____17279 =
                                                      let uu____17280 =
                                                        let uu____17291 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17291) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17280 in
                                                    (uu____17279,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17272 in
                                                [uu____17271])
                                       | uu____17308 -> [])) in
                             let uu____17309 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17309 with
                              | (vars,guards,env',decls1,uu____17336) ->
                                  let uu____17349 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17358 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17358, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17360 =
                                          encode_formula p env' in
                                        (match uu____17360 with
                                         | (g,ds) ->
                                             let uu____17371 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17371,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17349 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17384 =
                                           let uu____17391 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17391) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17384 in
                                       let uu____17400 =
                                         let vname_decl =
                                           let uu____17408 =
                                             let uu____17419 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17429  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17419,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17408 in
                                         let uu____17438 =
                                           let env2 =
                                             let uu___150_17444 = env1 in
                                             {
                                               bindings =
                                                 (uu___150_17444.bindings);
                                               depth = (uu___150_17444.depth);
                                               tcenv = (uu___150_17444.tcenv);
                                               warn = (uu___150_17444.warn);
                                               cache = (uu___150_17444.cache);
                                               nolabels =
                                                 (uu___150_17444.nolabels);
                                               use_zfuel_name =
                                                 (uu___150_17444.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___150_17444.current_module_name)
                                             } in
                                           let uu____17445 =
                                             let uu____17446 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17446 in
                                           if uu____17445
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17438 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17461::uu____17462 ->
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
                                                     let uu____17502 =
                                                       let uu____17513 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17513) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17502 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17540 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17543 =
                                               match formals with
                                               | [] ->
                                                   let uu____17560 =
                                                     let uu____17561 =
                                                       let uu____17564 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17564 in
                                                     push_free_var env1 lid
                                                       vname uu____17561 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17560)
                                               | uu____17569 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17576 =
                                                       let uu____17583 =
                                                         let uu____17584 =
                                                           let uu____17595 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17595) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17584 in
                                                       (uu____17583,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17576 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17543 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17400 with
                                        | (decls2,env2) ->
                                            let uu____17638 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17646 =
                                                encode_term res_t1 env' in
                                              match uu____17646 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17659 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17659, decls) in
                                            (match uu____17638 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17670 =
                                                     let uu____17677 =
                                                       let uu____17678 =
                                                         let uu____17689 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17689) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17678 in
                                                     (uu____17677,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17670 in
                                                 let freshness =
                                                   let uu____17705 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17705
                                                   then
                                                     let uu____17710 =
                                                       let uu____17711 =
                                                         let uu____17722 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17733 =
                                                           varops.next_id () in
                                                         (vname, uu____17722,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17733) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17711 in
                                                     let uu____17736 =
                                                       let uu____17739 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17739] in
                                                     uu____17710 ::
                                                       uu____17736
                                                   else [] in
                                                 let g =
                                                   let uu____17744 =
                                                     let uu____17747 =
                                                       let uu____17750 =
                                                         let uu____17753 =
                                                           let uu____17756 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17756 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17753 in
                                                       FStar_List.append
                                                         decls3 uu____17750 in
                                                     FStar_List.append decls2
                                                       uu____17747 in
                                                   FStar_List.append decls11
                                                     uu____17744 in
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
          let uu____17791 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17791 with
          | FStar_Pervasives_Native.None  ->
              let uu____17828 = encode_free_var false env x t t_norm [] in
              (match uu____17828 with
               | (decls,env1) ->
                   let uu____17855 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17855 with
                    | (n1,x',uu____17882) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17903) ->
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
            let uu____17963 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17963 with
            | (decls,env1) ->
                let uu____17982 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17982
                then
                  let uu____17989 =
                    let uu____17992 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17992 in
                  (uu____17989, env1)
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
             (fun uu____18047  ->
                fun lb  ->
                  match uu____18047 with
                  | (decls,env1) ->
                      let uu____18067 =
                        let uu____18074 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18074
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18067 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18096 = FStar_Syntax_Util.head_and_args t in
    match uu____18096 with
    | (hd1,args) ->
        let uu____18133 =
          let uu____18134 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18134.FStar_Syntax_Syntax.n in
        (match uu____18133 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18138,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18157 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18182  ->
      fun quals  ->
        match uu____18182 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18258 = FStar_Util.first_N nbinders formals in
              match uu____18258 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18339  ->
                         fun uu____18340  ->
                           match (uu____18339, uu____18340) with
                           | ((formal,uu____18358),(binder,uu____18360)) ->
                               let uu____18369 =
                                 let uu____18376 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18376) in
                               FStar_Syntax_Syntax.NT uu____18369) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18384 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18415  ->
                              match uu____18415 with
                              | (x,i) ->
                                  let uu____18426 =
                                    let uu___151_18427 = x in
                                    let uu____18428 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___151_18427.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___151_18427.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18428
                                    } in
                                  (uu____18426, i))) in
                    FStar_All.pipe_right uu____18384
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18446 =
                      let uu____18447 = FStar_Syntax_Subst.compress body in
                      let uu____18448 =
                        let uu____18449 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18449 in
                      FStar_Syntax_Syntax.extend_app_n uu____18447
                        uu____18448 in
                    uu____18446 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18510 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18510
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___152_18513 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_18513.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_18513.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_18513.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_18513.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_18513.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_18513.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_18513.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_18513.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_18513.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_18513.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_18513.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_18513.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_18513.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_18513.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_18513.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_18513.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_18513.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_18513.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_18513.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___152_18513.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___152_18513.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___152_18513.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_18513.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_18513.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_18513.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_18513.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___152_18513.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___152_18513.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___152_18513.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___152_18513.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___152_18513.FStar_TypeChecker_Env.tc_hooks)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18546 = FStar_Syntax_Util.abs_formals e in
                match uu____18546 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18610::uu____18611 ->
                         let uu____18626 =
                           let uu____18627 =
                             let uu____18630 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18630 in
                           uu____18627.FStar_Syntax_Syntax.n in
                         (match uu____18626 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18673 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18673 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18715 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18715
                                   then
                                     let uu____18750 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18750 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18844  ->
                                                   fun uu____18845  ->
                                                     match (uu____18844,
                                                             uu____18845)
                                                     with
                                                     | ((x,uu____18863),
                                                        (b,uu____18865)) ->
                                                         let uu____18874 =
                                                           let uu____18881 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18881) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18874)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18883 =
                                            let uu____18904 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18904) in
                                          (uu____18883, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18972 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18972 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19061) ->
                              let uu____19066 =
                                let uu____19087 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19087 in
                              (uu____19066, true)
                          | uu____19152 when Prims.op_Negation norm1 ->
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
                          | uu____19154 ->
                              let uu____19155 =
                                let uu____19156 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19157 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19156
                                  uu____19157 in
                              failwith uu____19155)
                     | uu____19182 ->
                         let uu____19183 =
                           let uu____19184 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19184.FStar_Syntax_Syntax.n in
                         (match uu____19183 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19229 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19229 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19261 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19261 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19344 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19400 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19400
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19412 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19506  ->
                            fun lb  ->
                              match uu____19506 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19601 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19601
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19604 =
                                      let uu____19619 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19619
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19604 with
                                    | (tok,decl,env2) ->
                                        let uu____19665 =
                                          let uu____19678 =
                                            let uu____19689 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19689, tok) in
                                          uu____19678 :: toks in
                                        (uu____19665, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19412 with
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
                        | uu____19872 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19880 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19880 vars)
                            else
                              (let uu____19882 =
                                 let uu____19889 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19889) in
                               FStar_SMTEncoding_Util.mkApp uu____19882) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19971;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19973;
                             FStar_Syntax_Syntax.lbeff = uu____19974;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20037 =
                              let uu____20044 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20044 with
                              | (tcenv',uu____20062,e_t) ->
                                  let uu____20068 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20079 -> failwith "Impossible" in
                                  (match uu____20068 with
                                   | (e1,t_norm1) ->
                                       ((let uu___155_20095 = env2 in
                                         {
                                           bindings =
                                             (uu___155_20095.bindings);
                                           depth = (uu___155_20095.depth);
                                           tcenv = tcenv';
                                           warn = (uu___155_20095.warn);
                                           cache = (uu___155_20095.cache);
                                           nolabels =
                                             (uu___155_20095.nolabels);
                                           use_zfuel_name =
                                             (uu___155_20095.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___155_20095.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___155_20095.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20037 with
                             | (env',e1,t_norm1) ->
                                 let uu____20105 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20105 with
                                  | ((binders,body,uu____20126,uu____20127),curry)
                                      ->
                                      ((let uu____20138 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20138
                                        then
                                          let uu____20139 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20140 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20139 uu____20140
                                        else ());
                                       (let uu____20142 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20142 with
                                        | (vars,guards,env'1,binder_decls,uu____20169)
                                            ->
                                            let body1 =
                                              let uu____20183 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20183
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20186 =
                                              let uu____20195 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20195
                                              then
                                                let uu____20206 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20207 =
                                                  encode_formula body1 env'1 in
                                                (uu____20206, uu____20207)
                                              else
                                                (let uu____20217 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20217)) in
                                            (match uu____20186 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20240 =
                                                     let uu____20247 =
                                                       let uu____20248 =
                                                         let uu____20259 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20259) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20248 in
                                                     let uu____20270 =
                                                       let uu____20273 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20273 in
                                                     (uu____20247,
                                                       uu____20270,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20240 in
                                                 let uu____20276 =
                                                   let uu____20279 =
                                                     let uu____20282 =
                                                       let uu____20285 =
                                                         let uu____20288 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20288 in
                                                       FStar_List.append
                                                         decls2 uu____20285 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20282 in
                                                   FStar_List.append decls1
                                                     uu____20279 in
                                                 (uu____20276, env2))))))
                        | uu____20293 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20378 = varops.fresh "fuel" in
                          (uu____20378, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20381 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20469  ->
                                  fun uu____20470  ->
                                    match (uu____20469, uu____20470) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20618 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20618 in
                                        let gtok =
                                          let uu____20620 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20620 in
                                        let env4 =
                                          let uu____20622 =
                                            let uu____20625 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20625 in
                                          push_free_var env3 flid gtok
                                            uu____20622 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20381 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20781 t_norm
                              uu____20783 =
                              match (uu____20781, uu____20783) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20827;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20828;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20856 =
                                    let uu____20863 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20863 with
                                    | (tcenv',uu____20885,e_t) ->
                                        let uu____20891 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20902 ->
                                              failwith "Impossible" in
                                        (match uu____20891 with
                                         | (e1,t_norm1) ->
                                             ((let uu___156_20918 = env3 in
                                               {
                                                 bindings =
                                                   (uu___156_20918.bindings);
                                                 depth =
                                                   (uu___156_20918.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___156_20918.warn);
                                                 cache =
                                                   (uu___156_20918.cache);
                                                 nolabels =
                                                   (uu___156_20918.nolabels);
                                                 use_zfuel_name =
                                                   (uu___156_20918.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___156_20918.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___156_20918.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20856 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20933 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20933
                                         then
                                           let uu____20934 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20935 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20936 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20934 uu____20935
                                             uu____20936
                                         else ());
                                        (let uu____20938 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20938 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20975 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20975
                                               then
                                                 let uu____20976 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20977 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20978 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20979 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20976 uu____20977
                                                   uu____20978 uu____20979
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20983 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20983 with
                                               | (vars,guards,env'1,binder_decls,uu____21014)
                                                   ->
                                                   let decl_g =
                                                     let uu____21028 =
                                                       let uu____21039 =
                                                         let uu____21042 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21042 in
                                                       (g, uu____21039,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21028 in
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
                                                     let uu____21067 =
                                                       let uu____21074 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21074) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21067 in
                                                   let gsapp =
                                                     let uu____21084 =
                                                       let uu____21091 =
                                                         let uu____21094 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21094 ::
                                                           vars_tm in
                                                       (g, uu____21091) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21084 in
                                                   let gmax =
                                                     let uu____21100 =
                                                       let uu____21107 =
                                                         let uu____21110 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21110 ::
                                                           vars_tm in
                                                       (g, uu____21107) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21100 in
                                                   let body1 =
                                                     let uu____21116 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21116
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21118 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21118 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21136 =
                                                            let uu____21143 =
                                                              let uu____21144
                                                                =
                                                                let uu____21159
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
                                                                  uu____21159) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21144 in
                                                            let uu____21180 =
                                                              let uu____21183
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21183 in
                                                            (uu____21143,
                                                              uu____21180,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21136 in
                                                        let eqn_f =
                                                          let uu____21187 =
                                                            let uu____21194 =
                                                              let uu____21195
                                                                =
                                                                let uu____21206
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21206) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21195 in
                                                            (uu____21194,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21187 in
                                                        let eqn_g' =
                                                          let uu____21220 =
                                                            let uu____21227 =
                                                              let uu____21228
                                                                =
                                                                let uu____21239
                                                                  =
                                                                  let uu____21240
                                                                    =
                                                                    let uu____21245
                                                                    =
                                                                    let uu____21246
                                                                    =
                                                                    let uu____21253
                                                                    =
                                                                    let uu____21256
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21256
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21253) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21246 in
                                                                    (gsapp,
                                                                    uu____21245) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21240 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21239) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21228 in
                                                            (uu____21227,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21220 in
                                                        let uu____21279 =
                                                          let uu____21288 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21288
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21317)
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
                                                                  let uu____21342
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21342
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21347
                                                                  =
                                                                  let uu____21354
                                                                    =
                                                                    let uu____21355
                                                                    =
                                                                    let uu____21366
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21366) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21355 in
                                                                  (uu____21354,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21347 in
                                                              let uu____21387
                                                                =
                                                                let uu____21394
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21394
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21407
                                                                    =
                                                                    let uu____21410
                                                                    =
                                                                    let uu____21411
                                                                    =
                                                                    let uu____21418
                                                                    =
                                                                    let uu____21419
                                                                    =
                                                                    let uu____21430
                                                                    =
                                                                    let uu____21431
                                                                    =
                                                                    let uu____21436
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21436,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21431 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21430) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21419 in
                                                                    (uu____21418,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21411 in
                                                                    [uu____21410] in
                                                                    (d3,
                                                                    uu____21407) in
                                                              (match uu____21387
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21279
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
                            let uu____21501 =
                              let uu____21514 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21593  ->
                                   fun uu____21594  ->
                                     match (uu____21593, uu____21594) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21749 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21749 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21514 in
                            (match uu____21501 with
                             | (decls2,eqns,env01) ->
                                 let uu____21822 =
                                   let isDeclFun uu___122_21834 =
                                     match uu___122_21834 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21835 -> true
                                     | uu____21846 -> false in
                                   let uu____21847 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21847
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21822 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21887 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___123_21891  ->
                                 match uu___123_21891 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21892 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21898 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21898))) in
                      if uu____21887
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
                   let uu____21950 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21950
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
        let uu____21999 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21999 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22003 = encode_sigelt' env se in
      match uu____22003 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22019 =
                  let uu____22020 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22020 in
                [uu____22019]
            | uu____22021 ->
                let uu____22022 =
                  let uu____22025 =
                    let uu____22026 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22026 in
                  uu____22025 :: g in
                let uu____22027 =
                  let uu____22030 =
                    let uu____22031 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22031 in
                  [uu____22030] in
                FStar_List.append uu____22022 uu____22027 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22044 =
          let uu____22045 = FStar_Syntax_Subst.compress t in
          uu____22045.FStar_Syntax_Syntax.n in
        match uu____22044 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22049)) -> s = "opaque_to_smt"
        | uu____22050 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22055 =
          let uu____22056 = FStar_Syntax_Subst.compress t in
          uu____22056.FStar_Syntax_Syntax.n in
        match uu____22055 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22060)) -> s = "uninterpreted_by_smt"
        | uu____22061 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22066 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22071 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22074 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22077 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22092 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22096 =
            let uu____22097 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22097 Prims.op_Negation in
          if uu____22096
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22123 ->
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
               let uu____22143 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22143 with
               | (aname,atok,env2) ->
                   let uu____22159 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22159 with
                    | (formals,uu____22177) ->
                        let uu____22190 =
                          let uu____22195 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22195 env2 in
                        (match uu____22190 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22207 =
                                 let uu____22208 =
                                   let uu____22219 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22235  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22219,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22208 in
                               [uu____22207;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22248 =
                               let aux uu____22300 uu____22301 =
                                 match (uu____22300, uu____22301) with
                                 | ((bv,uu____22353),(env3,acc_sorts,acc)) ->
                                     let uu____22391 = gen_term_var env3 bv in
                                     (match uu____22391 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22248 with
                              | (uu____22463,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22486 =
                                      let uu____22493 =
                                        let uu____22494 =
                                          let uu____22505 =
                                            let uu____22506 =
                                              let uu____22511 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22511) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22506 in
                                          ([[app]], xs_sorts, uu____22505) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22494 in
                                      (uu____22493,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22486 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22531 =
                                      let uu____22538 =
                                        let uu____22539 =
                                          let uu____22550 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22550) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22539 in
                                      (uu____22538,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22531 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22569 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22569 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22597,uu____22598)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22599 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22599 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22616,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22622 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___124_22626  ->
                      match uu___124_22626 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22627 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22632 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22633 -> false)) in
            Prims.op_Negation uu____22622 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22642 =
               let uu____22649 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22649 env fv t quals in
             match uu____22642 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22664 =
                   let uu____22667 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22667 in
                 (uu____22664, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22675 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22675 with
           | (uu____22684,f1) ->
               let uu____22686 = encode_formula f1 env in
               (match uu____22686 with
                | (f2,decls) ->
                    let g =
                      let uu____22700 =
                        let uu____22701 =
                          let uu____22708 =
                            let uu____22711 =
                              let uu____22712 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22712 in
                            FStar_Pervasives_Native.Some uu____22711 in
                          let uu____22713 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22708, uu____22713) in
                        FStar_SMTEncoding_Util.mkAssume uu____22701 in
                      [uu____22700] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22719) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22731 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22749 =
                       let uu____22752 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22752.FStar_Syntax_Syntax.fv_name in
                     uu____22749.FStar_Syntax_Syntax.v in
                   let uu____22753 =
                     let uu____22754 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22754 in
                   if uu____22753
                   then
                     let val_decl =
                       let uu___159_22782 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___159_22782.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___159_22782.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___159_22782.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22787 = encode_sigelt' env1 val_decl in
                     match uu____22787 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22731 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22815,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22817;
                          FStar_Syntax_Syntax.lbtyp = uu____22818;
                          FStar_Syntax_Syntax.lbeff = uu____22819;
                          FStar_Syntax_Syntax.lbdef = uu____22820;_}::[]),uu____22821)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22840 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22840 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22869 =
                   let uu____22872 =
                     let uu____22873 =
                       let uu____22880 =
                         let uu____22881 =
                           let uu____22892 =
                             let uu____22893 =
                               let uu____22898 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22898) in
                             FStar_SMTEncoding_Util.mkEq uu____22893 in
                           ([[b2t_x]], [xx], uu____22892) in
                         FStar_SMTEncoding_Util.mkForall uu____22881 in
                       (uu____22880,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22873 in
                   [uu____22872] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22869 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22931,uu____22932) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_22941  ->
                  match uu___125_22941 with
                  | FStar_Syntax_Syntax.Discriminator uu____22942 -> true
                  | uu____22943 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22946,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22957 =
                     let uu____22958 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22958.FStar_Ident.idText in
                   uu____22957 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___126_22962  ->
                     match uu___126_22962 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22963 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22967) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___127_22984  ->
                  match uu___127_22984 with
                  | FStar_Syntax_Syntax.Projector uu____22985 -> true
                  | uu____22990 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22993 = try_lookup_free_var env l in
          (match uu____22993 with
           | FStar_Pervasives_Native.Some uu____23000 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___160_23004 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___160_23004.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___160_23004.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___160_23004.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23011) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23029) ->
          let uu____23038 = encode_sigelts env ses in
          (match uu____23038 with
           | (g,env1) ->
               let uu____23055 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___128_23078  ->
                         match uu___128_23078 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23079;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23080;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23081;_}
                             -> false
                         | uu____23084 -> true)) in
               (match uu____23055 with
                | (g',inversions) ->
                    let uu____23099 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___129_23120  ->
                              match uu___129_23120 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23121 ->
                                  true
                              | uu____23132 -> false)) in
                    (match uu____23099 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23150,tps,k,uu____23153,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___130_23170  ->
                    match uu___130_23170 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23171 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23180 = c in
              match uu____23180 with
              | (name,args,uu____23185,uu____23186,uu____23187) ->
                  let uu____23192 =
                    let uu____23193 =
                      let uu____23204 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23221  ->
                                match uu____23221 with
                                | (uu____23228,sort,uu____23230) -> sort)) in
                      (name, uu____23204, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23193 in
                  [uu____23192]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23257 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23263 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23263 FStar_Option.isNone)) in
            if uu____23257
            then []
            else
              (let uu____23295 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23295 with
               | (xxsym,xx) ->
                   let uu____23304 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23343  ->
                             fun l  ->
                               match uu____23343 with
                               | (out,decls) ->
                                   let uu____23363 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23363 with
                                    | (uu____23374,data_t) ->
                                        let uu____23376 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23376 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23422 =
                                                 let uu____23423 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23423.FStar_Syntax_Syntax.n in
                                               match uu____23422 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23434,indices) ->
                                                   indices
                                               | uu____23456 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23480  ->
                                                         match uu____23480
                                                         with
                                                         | (x,uu____23486) ->
                                                             let uu____23487
                                                               =
                                                               let uu____23488
                                                                 =
                                                                 let uu____23495
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23495,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23488 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23487)
                                                    env) in
                                             let uu____23498 =
                                               encode_args indices env1 in
                                             (match uu____23498 with
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
                                                      let uu____23524 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23540
                                                                 =
                                                                 let uu____23545
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23545,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23540)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23524
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23548 =
                                                      let uu____23549 =
                                                        let uu____23554 =
                                                          let uu____23555 =
                                                            let uu____23560 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23560,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23555 in
                                                        (out, uu____23554) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23549 in
                                                    (uu____23548,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23304 with
                    | (data_ax,decls) ->
                        let uu____23573 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23573 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23584 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23584 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23588 =
                                 let uu____23595 =
                                   let uu____23596 =
                                     let uu____23607 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23622 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23607,
                                       uu____23622) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23596 in
                                 let uu____23637 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23595,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23637) in
                               FStar_SMTEncoding_Util.mkAssume uu____23588 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23640 =
            let uu____23653 =
              let uu____23654 = FStar_Syntax_Subst.compress k in
              uu____23654.FStar_Syntax_Syntax.n in
            match uu____23653 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23699 -> (tps, k) in
          (match uu____23640 with
           | (formals,res) ->
               let uu____23722 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23722 with
                | (formals1,res1) ->
                    let uu____23733 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23733 with
                     | (vars,guards,env',binder_decls,uu____23758) ->
                         let uu____23771 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23771 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23790 =
                                  let uu____23797 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23797) in
                                FStar_SMTEncoding_Util.mkApp uu____23790 in
                              let uu____23806 =
                                let tname_decl =
                                  let uu____23816 =
                                    let uu____23817 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23849  ->
                                              match uu____23849 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23862 = varops.next_id () in
                                    (tname, uu____23817,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23862, false) in
                                  constructor_or_logic_type_decl uu____23816 in
                                let uu____23871 =
                                  match vars with
                                  | [] ->
                                      let uu____23884 =
                                        let uu____23885 =
                                          let uu____23888 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23888 in
                                        push_free_var env1 t tname
                                          uu____23885 in
                                      ([], uu____23884)
                                  | uu____23895 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23904 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23904 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23918 =
                                          let uu____23925 =
                                            let uu____23926 =
                                              let uu____23941 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23941) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23926 in
                                          (uu____23925,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23918 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23871 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23806 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23981 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23981 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23999 =
                                               let uu____24000 =
                                                 let uu____24007 =
                                                   let uu____24008 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24008 in
                                                 (uu____24007,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24000 in
                                             [uu____23999]
                                           else [] in
                                         let uu____24012 =
                                           let uu____24015 =
                                             let uu____24018 =
                                               let uu____24019 =
                                                 let uu____24026 =
                                                   let uu____24027 =
                                                     let uu____24038 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24038) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24027 in
                                                 (uu____24026,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24019 in
                                             [uu____24018] in
                                           FStar_List.append karr uu____24015 in
                                         FStar_List.append decls1 uu____24012 in
                                   let aux =
                                     let uu____24054 =
                                       let uu____24057 =
                                         inversion_axioms tapp vars in
                                       let uu____24060 =
                                         let uu____24063 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24063] in
                                       FStar_List.append uu____24057
                                         uu____24060 in
                                     FStar_List.append kindingAx uu____24054 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24070,uu____24071,uu____24072,uu____24073,uu____24074)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24082,t,uu____24084,n_tps,uu____24086) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24094 = new_term_constant_and_tok_from_lid env d in
          (match uu____24094 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24111 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24111 with
                | (formals,t_res) ->
                    let uu____24146 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24146 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24160 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24160 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24230 =
                                            mk_term_projector_name d x in
                                          (uu____24230,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24232 =
                                  let uu____24251 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24251, true) in
                                FStar_All.pipe_right uu____24232
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
                              let uu____24290 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24290 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24302::uu____24303 ->
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
                                         let uu____24348 =
                                           let uu____24359 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24359) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24348
                                     | uu____24384 -> tok_typing in
                                   let uu____24393 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24393 with
                                    | (vars',guards',env'',decls_formals,uu____24418)
                                        ->
                                        let uu____24431 =
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
                                        (match uu____24431 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24462 ->
                                                   let uu____24469 =
                                                     let uu____24470 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24470 in
                                                   [uu____24469] in
                                             let encode_elim uu____24480 =
                                               let uu____24481 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24481 with
                                               | (head1,args) ->
                                                   let uu____24524 =
                                                     let uu____24525 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24525.FStar_Syntax_Syntax.n in
                                                   (match uu____24524 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24535;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24536;_},uu____24537)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24543 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24543
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
                                                                 | uu____24586
                                                                    ->
                                                                    let uu____24587
                                                                    =
                                                                    let uu____24588
                                                                    =
                                                                    let uu____24593
                                                                    =
                                                                    let uu____24594
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24594 in
                                                                    (uu____24593,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24588 in
                                                                    FStar_Exn.raise
                                                                    uu____24587 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24610
                                                                    =
                                                                    let uu____24611
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24611 in
                                                                    if
                                                                    uu____24610
                                                                    then
                                                                    let uu____24624
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24624]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24626
                                                               =
                                                               let uu____24639
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24689
                                                                     ->
                                                                    fun
                                                                    uu____24690
                                                                     ->
                                                                    match 
                                                                    (uu____24689,
                                                                    uu____24690)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24785
                                                                    =
                                                                    let uu____24792
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24792 in
                                                                    (match uu____24785
                                                                    with
                                                                    | 
                                                                    (uu____24805,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24813
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24813
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24815
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24815
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
                                                                 uu____24639 in
                                                             (match uu____24626
                                                              with
                                                              | (uu____24830,arg_vars,elim_eqns_or_guards,uu____24833)
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
                                                                    let uu____24863
                                                                    =
                                                                    let uu____24870
                                                                    =
                                                                    let uu____24871
                                                                    =
                                                                    let uu____24882
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24893
                                                                    =
                                                                    let uu____24894
                                                                    =
                                                                    let uu____24899
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24899) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24894 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24882,
                                                                    uu____24893) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24871 in
                                                                    (uu____24870,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24863 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24922
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24922,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24924
                                                                    =
                                                                    let uu____24931
                                                                    =
                                                                    let uu____24932
                                                                    =
                                                                    let uu____24943
                                                                    =
                                                                    let uu____24948
                                                                    =
                                                                    let uu____24951
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24951] in
                                                                    [uu____24948] in
                                                                    let uu____24956
                                                                    =
                                                                    let uu____24957
                                                                    =
                                                                    let uu____24962
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24963
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24962,
                                                                    uu____24963) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24957 in
                                                                    (uu____24943,
                                                                    [x],
                                                                    uu____24956) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24932 in
                                                                    let uu____24982
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24931,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24982) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24924
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24989
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
                                                                    (let uu____25017
                                                                    =
                                                                    let uu____25018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25018
                                                                    dapp1 in
                                                                    [uu____25017]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24989
                                                                    FStar_List.flatten in
                                                                    let uu____25025
                                                                    =
                                                                    let uu____25032
                                                                    =
                                                                    let uu____25033
                                                                    =
                                                                    let uu____25044
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25055
                                                                    =
                                                                    let uu____25056
                                                                    =
                                                                    let uu____25061
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25061) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25056 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25044,
                                                                    uu____25055) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25033 in
                                                                    (uu____25032,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25025) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25082 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25082
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
                                                                 | uu____25125
                                                                    ->
                                                                    let uu____25126
                                                                    =
                                                                    let uu____25127
                                                                    =
                                                                    let uu____25132
                                                                    =
                                                                    let uu____25133
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25133 in
                                                                    (uu____25132,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25127 in
                                                                    FStar_Exn.raise
                                                                    uu____25126 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25149
                                                                    =
                                                                    let uu____25150
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25150 in
                                                                    if
                                                                    uu____25149
                                                                    then
                                                                    let uu____25163
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25163]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25165
                                                               =
                                                               let uu____25178
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25228
                                                                     ->
                                                                    fun
                                                                    uu____25229
                                                                     ->
                                                                    match 
                                                                    (uu____25228,
                                                                    uu____25229)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25324
                                                                    =
                                                                    let uu____25331
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25331 in
                                                                    (match uu____25324
                                                                    with
                                                                    | 
                                                                    (uu____25344,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25352
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25352
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25354
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
                                                                 uu____25178 in
                                                             (match uu____25165
                                                              with
                                                              | (uu____25369,arg_vars,elim_eqns_or_guards,uu____25372)
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
                                                                    let uu____25402
                                                                    =
                                                                    let uu____25409
                                                                    =
                                                                    let uu____25410
                                                                    =
                                                                    let uu____25421
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25432
                                                                    =
                                                                    let uu____25433
                                                                    =
                                                                    let uu____25438
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25438) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25433 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25421,
                                                                    uu____25432) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25410 in
                                                                    (uu____25409,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25402 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25461
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25461,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25463
                                                                    =
                                                                    let uu____25470
                                                                    =
                                                                    let uu____25471
                                                                    =
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25487
                                                                    =
                                                                    let uu____25490
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25490] in
                                                                    [uu____25487] in
                                                                    let uu____25495
                                                                    =
                                                                    let uu____25496
                                                                    =
                                                                    let uu____25501
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25501,
                                                                    uu____25502) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25496 in
                                                                    (uu____25482,
                                                                    [x],
                                                                    uu____25495) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25471 in
                                                                    let uu____25521
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25470,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25521) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25463
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25528
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
                                                                    (let uu____25556
                                                                    =
                                                                    let uu____25557
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25557
                                                                    dapp1 in
                                                                    [uu____25556]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25528
                                                                    FStar_List.flatten in
                                                                    let uu____25564
                                                                    =
                                                                    let uu____25571
                                                                    =
                                                                    let uu____25572
                                                                    =
                                                                    let uu____25583
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25594
                                                                    =
                                                                    let uu____25595
                                                                    =
                                                                    let uu____25600
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25600) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25595 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25583,
                                                                    uu____25594) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25572 in
                                                                    (uu____25571,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25564) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25619 ->
                                                        ((let uu____25621 =
                                                            let uu____25622 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25623 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25622
                                                              uu____25623 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25621);
                                                         ([], []))) in
                                             let uu____25628 = encode_elim () in
                                             (match uu____25628 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25648 =
                                                      let uu____25651 =
                                                        let uu____25654 =
                                                          let uu____25657 =
                                                            let uu____25660 =
                                                              let uu____25661
                                                                =
                                                                let uu____25672
                                                                  =
                                                                  let uu____25675
                                                                    =
                                                                    let uu____25676
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25676 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25675 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25672) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25661 in
                                                            [uu____25660] in
                                                          let uu____25681 =
                                                            let uu____25684 =
                                                              let uu____25687
                                                                =
                                                                let uu____25690
                                                                  =
                                                                  let uu____25693
                                                                    =
                                                                    let uu____25696
                                                                    =
                                                                    let uu____25699
                                                                    =
                                                                    let uu____25700
                                                                    =
                                                                    let uu____25707
                                                                    =
                                                                    let uu____25708
                                                                    =
                                                                    let uu____25719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25719) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25708 in
                                                                    (uu____25707,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25700 in
                                                                    let uu____25732
                                                                    =
                                                                    let uu____25735
                                                                    =
                                                                    let uu____25736
                                                                    =
                                                                    let uu____25743
                                                                    =
                                                                    let uu____25744
                                                                    =
                                                                    let uu____25755
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25766
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25755,
                                                                    uu____25766) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25744 in
                                                                    (uu____25743,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25736 in
                                                                    [uu____25735] in
                                                                    uu____25699
                                                                    ::
                                                                    uu____25732 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25696 in
                                                                  FStar_List.append
                                                                    uu____25693
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25690 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25687 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25684 in
                                                          FStar_List.append
                                                            uu____25657
                                                            uu____25681 in
                                                        FStar_List.append
                                                          decls3 uu____25654 in
                                                      FStar_List.append
                                                        decls2 uu____25651 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25648 in
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
           (fun uu____25812  ->
              fun se  ->
                match uu____25812 with
                | (g,env1) ->
                    let uu____25832 = encode_sigelt env1 se in
                    (match uu____25832 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25891 =
        match uu____25891 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25923 ->
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
                 ((let uu____25929 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25929
                   then
                     let uu____25930 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25931 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25932 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25930 uu____25931 uu____25932
                   else ());
                  (let uu____25934 = encode_term t1 env1 in
                   match uu____25934 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25950 =
                         let uu____25957 =
                           let uu____25958 =
                             let uu____25959 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25959
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25958 in
                         new_term_constant_from_string env1 x uu____25957 in
                       (match uu____25950 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25975 = FStar_Options.log_queries () in
                              if uu____25975
                              then
                                let uu____25978 =
                                  let uu____25979 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25980 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25981 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25979 uu____25980 uu____25981 in
                                FStar_Pervasives_Native.Some uu____25978
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25997,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26011 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26011 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26034,se,uu____26036) ->
                 let uu____26041 = encode_sigelt env1 se in
                 (match uu____26041 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26058,se) ->
                 let uu____26064 = encode_sigelt env1 se in
                 (match uu____26064 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26081 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26081 with | (uu____26104,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26119 'Auu____26120 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26120,'Auu____26119)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26188  ->
              match uu____26188 with
              | (l,uu____26200,uu____26201) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26247  ->
              match uu____26247 with
              | (l,uu____26261,uu____26262) ->
                  let uu____26271 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26272 =
                    let uu____26275 =
                      let uu____26276 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26276 in
                    [uu____26275] in
                  uu____26271 :: uu____26272)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26298 =
      let uu____26301 =
        let uu____26302 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26305 =
          let uu____26306 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26306 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26302;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26305
        } in
      [uu____26301] in
    FStar_ST.op_Colon_Equals last_env uu____26298
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26365 = FStar_ST.op_Bang last_env in
      match uu____26365 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26419 ->
          let uu___161_26422 = e in
          let uu____26423 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_26422.bindings);
            depth = (uu___161_26422.depth);
            tcenv;
            warn = (uu___161_26422.warn);
            cache = (uu___161_26422.cache);
            nolabels = (uu___161_26422.nolabels);
            use_zfuel_name = (uu___161_26422.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_26422.encode_non_total_function_typ);
            current_module_name = uu____26423
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26428 = FStar_ST.op_Bang last_env in
    match uu____26428 with
    | [] -> failwith "Empty env stack"
    | uu____26481::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26538  ->
    let uu____26539 = FStar_ST.op_Bang last_env in
    match uu____26539 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_26600 = hd1 in
          {
            bindings = (uu___162_26600.bindings);
            depth = (uu___162_26600.depth);
            tcenv = (uu___162_26600.tcenv);
            warn = (uu___162_26600.warn);
            cache = refs;
            nolabels = (uu___162_26600.nolabels);
            use_zfuel_name = (uu___162_26600.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_26600.encode_non_total_function_typ);
            current_module_name = (uu___162_26600.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26654  ->
    let uu____26655 = FStar_ST.op_Bang last_env in
    match uu____26655 with
    | [] -> failwith "Popping an empty stack"
    | uu____26708::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26806::uu____26807,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___163_26815 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___163_26815.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___163_26815.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___163_26815.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26816 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26833 =
        let uu____26836 =
          let uu____26837 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26837 in
        let uu____26838 = open_fact_db_tags env in uu____26836 :: uu____26838 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26833
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
      let uu____26862 = encode_sigelt env se in
      match uu____26862 with
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
        let uu____26900 = FStar_Options.log_queries () in
        if uu____26900
        then
          let uu____26903 =
            let uu____26904 =
              let uu____26905 =
                let uu____26906 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26906 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26905 in
            FStar_SMTEncoding_Term.Caption uu____26904 in
          uu____26903 :: decls
        else decls in
      (let uu____26917 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26917
       then
         let uu____26918 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26918
       else ());
      (let env =
         let uu____26921 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26921 tcenv in
       let uu____26922 = encode_top_level_facts env se in
       match uu____26922 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26936 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26936)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26950 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26950
       then
         let uu____26951 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26951
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26986  ->
                 fun se  ->
                   match uu____26986 with
                   | (g,env2) ->
                       let uu____27006 = encode_top_level_facts env2 se in
                       (match uu____27006 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27029 =
         encode_signature
           (let uu___164_27038 = env in
            {
              bindings = (uu___164_27038.bindings);
              depth = (uu___164_27038.depth);
              tcenv = (uu___164_27038.tcenv);
              warn = false;
              cache = (uu___164_27038.cache);
              nolabels = (uu___164_27038.nolabels);
              use_zfuel_name = (uu___164_27038.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___164_27038.encode_non_total_function_typ);
              current_module_name = (uu___164_27038.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27029 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27055 = FStar_Options.log_queries () in
             if uu____27055
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___165_27063 = env1 in
               {
                 bindings = (uu___165_27063.bindings);
                 depth = (uu___165_27063.depth);
                 tcenv = (uu___165_27063.tcenv);
                 warn = true;
                 cache = (uu___165_27063.cache);
                 nolabels = (uu___165_27063.nolabels);
                 use_zfuel_name = (uu___165_27063.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___165_27063.encode_non_total_function_typ);
                 current_module_name = (uu___165_27063.current_module_name)
               });
            (let uu____27065 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27065
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
        (let uu____27120 =
           let uu____27121 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27121.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27120);
        (let env =
           let uu____27123 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27123 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27135 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27170 = aux rest in
                 (match uu____27170 with
                  | (out,rest1) ->
                      let t =
                        let uu____27200 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27200 with
                        | FStar_Pervasives_Native.Some uu____27205 ->
                            let uu____27206 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27206
                              x.FStar_Syntax_Syntax.sort
                        | uu____27207 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27211 =
                        let uu____27214 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___166_27217 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_27217.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_27217.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27214 :: out in
                      (uu____27211, rest1))
             | uu____27222 -> ([], bindings1) in
           let uu____27229 = aux bindings in
           match uu____27229 with
           | (closing,bindings1) ->
               let uu____27254 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27254, bindings1) in
         match uu____27135 with
         | (q1,bindings1) ->
             let uu____27277 =
               let uu____27282 =
                 FStar_List.filter
                   (fun uu___131_27287  ->
                      match uu___131_27287 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27288 ->
                          false
                      | uu____27295 -> true) bindings1 in
               encode_env_bindings env uu____27282 in
             (match uu____27277 with
              | (env_decls,env1) ->
                  ((let uu____27313 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27313
                    then
                      let uu____27314 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27314
                    else ());
                   (let uu____27316 = encode_formula q1 env1 in
                    match uu____27316 with
                    | (phi,qdecls) ->
                        let uu____27337 =
                          let uu____27342 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27342 phi in
                        (match uu____27337 with
                         | (labels,phi1) ->
                             let uu____27359 = encode_labels labels in
                             (match uu____27359 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27396 =
                                      let uu____27403 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27404 =
                                        varops.mk_unique "@query" in
                                      (uu____27403,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27404) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27396 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))