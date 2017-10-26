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
      (fun uu___132_119  ->
         match uu___132_119 with
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
        let uu___155_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___155_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___155_221.FStar_Syntax_Syntax.sort)
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
    let uu___156_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___156_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___156_1896.FStar_Syntax_Syntax.sort)
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
                 (fun uu___133_2369  ->
                    match uu___133_2369 with
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
           (fun uu___134_2394  ->
              match uu___134_2394 with
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
        (let uu___157_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___157_2483.tcenv);
           warn = (uu___157_2483.warn);
           cache = (uu___157_2483.cache);
           nolabels = (uu___157_2483.nolabels);
           use_zfuel_name = (uu___157_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___157_2483.encode_non_total_function_typ);
           current_module_name = (uu___157_2483.current_module_name)
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
        (let uu___158_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___158_2503.depth);
           tcenv = (uu___158_2503.tcenv);
           warn = (uu___158_2503.warn);
           cache = (uu___158_2503.cache);
           nolabels = (uu___158_2503.nolabels);
           use_zfuel_name = (uu___158_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___158_2503.encode_non_total_function_typ);
           current_module_name = (uu___158_2503.current_module_name)
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
          (let uu___159_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___159_2527.depth);
             tcenv = (uu___159_2527.tcenv);
             warn = (uu___159_2527.warn);
             cache = (uu___159_2527.cache);
             nolabels = (uu___159_2527.nolabels);
             use_zfuel_name = (uu___159_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___159_2527.encode_non_total_function_typ);
             current_module_name = (uu___159_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___160_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___160_2540.depth);
          tcenv = (uu___160_2540.tcenv);
          warn = (uu___160_2540.warn);
          cache = (uu___160_2540.cache);
          nolabels = (uu___160_2540.nolabels);
          use_zfuel_name = (uu___160_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___160_2540.encode_non_total_function_typ);
          current_module_name = (uu___160_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___135_2566  ->
             match uu___135_2566 with
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
        let uu___161_2639 = env in
        let uu____2640 =
          let uu____2643 =
            let uu____2644 =
              let uu____2657 =
                let uu____2660 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2660 in
              (x, fname, uu____2657, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2644 in
          uu____2643 :: (env.bindings) in
        {
          bindings = uu____2640;
          depth = (uu___161_2639.depth);
          tcenv = (uu___161_2639.tcenv);
          warn = (uu___161_2639.warn);
          cache = (uu___161_2639.cache);
          nolabels = (uu___161_2639.nolabels);
          use_zfuel_name = (uu___161_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___161_2639.encode_non_total_function_typ);
          current_module_name = (uu___161_2639.current_module_name)
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
        (fun uu___136_2704  ->
           match uu___136_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___137_2770  ->
             match uu___137_2770 with
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
          let uu___162_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___162_2892.depth);
            tcenv = (uu___162_2892.tcenv);
            warn = (uu___162_2892.warn);
            cache = (uu___162_2892.cache);
            nolabels = (uu___162_2892.nolabels);
            use_zfuel_name = (uu___162_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_2892.encode_non_total_function_typ);
            current_module_name = (uu___162_2892.current_module_name)
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
            let uu___163_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___163_2947.depth);
              tcenv = (uu___163_2947.tcenv);
              warn = (uu___163_2947.warn);
              cache = (uu___163_2947.cache);
              nolabels = (uu___163_2947.nolabels);
              use_zfuel_name = (uu___163_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___163_2947.encode_non_total_function_typ);
              current_module_name = (uu___163_2947.current_module_name)
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
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
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
        (fun uu___138_3201  ->
           match uu___138_3201 with
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
               (fun uu___139_3528  ->
                  match uu___139_3528 with
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
  fun uu___140_3636  ->
    match uu___140_3636 with
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3992 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4005 ->
            let uu____4012 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____4012
        | uu____4013 ->
            if norm1
            then let uu____4014 = whnf env t1 in aux false uu____4014
            else
              (let uu____4016 =
                 let uu____4017 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____4018 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4017 uu____4018 in
               failwith uu____4016) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____4051) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____4056 ->
        let uu____4057 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4057)
let is_arithmetic_primitive:
  'Auu____4074 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4074 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4094::uu____4095::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4099::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4102 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4124 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4140 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4147 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4147)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4186)::uu____4187::uu____4188::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4239)::uu____4240::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4277 -> false
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
          let uu____4484 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4484, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4487 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4487, [])
      | FStar_Const.Const_char c1 ->
          let uu____4491 =
            let uu____4492 =
              let uu____4499 =
                let uu____4502 =
                  let uu____4503 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4503 in
                [uu____4502] in
              ("FStar.Char.Char", uu____4499) in
            FStar_SMTEncoding_Util.mkApp uu____4492 in
          (uu____4491, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4519 =
            let uu____4520 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4520 in
          (uu____4519, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4541) ->
          let uu____4542 = varops.string_const s in (uu____4542, [])
      | FStar_Const.Const_range uu____4545 ->
          let uu____4546 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4546, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4552 =
            let uu____4553 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4553 in
          failwith uu____4552
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
        (let uu____4582 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4582
         then
           let uu____4583 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4583
         else ());
        (let uu____4585 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4669  ->
                   fun b  ->
                     match uu____4669 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4748 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4764 = gen_term_var env1 x in
                           match uu____4764 with
                           | (xxsym,xx,env') ->
                               let uu____4788 =
                                 let uu____4793 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4793 env1 xx in
                               (match uu____4788 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4748 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4585 with
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
          let uu____4952 = encode_term t env in
          match uu____4952 with
          | (t1,decls) ->
              let uu____4963 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4963, decls)
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
          let uu____4974 = encode_term t env in
          match uu____4974 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4989 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4989, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4991 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4991, decls))
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
        let uu____4997 = encode_args args_e env in
        match uu____4997 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5016 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5025 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5025 in
            let binary arg_tms1 =
              let uu____5038 =
                let uu____5039 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5039 in
              let uu____5040 =
                let uu____5041 =
                  let uu____5042 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5042 in
                FStar_SMTEncoding_Term.unboxInt uu____5041 in
              (uu____5038, uu____5040) in
            let mk_default uu____5048 =
              let uu____5049 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5049 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5100 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5100
              then
                let uu____5101 = let uu____5102 = mk_args ts in op uu____5102 in
                FStar_All.pipe_right uu____5101 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5131 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5131
              then
                let uu____5132 = binary ts in
                match uu____5132 with
                | (t1,t2) ->
                    let uu____5139 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5139
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5143 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5143
                 then
                   let uu____5144 = op (binary ts) in
                   FStar_All.pipe_right uu____5144
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
            let uu____5275 =
              let uu____5284 =
                FStar_List.tryFind
                  (fun uu____5306  ->
                     match uu____5306 with
                     | (l,uu____5316) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5284 FStar_Util.must in
            (match uu____5275 with
             | (uu____5355,op) ->
                 let uu____5365 = op arg_tms in (uu____5365, decls))
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
        let uu____5373 = FStar_List.hd args_e in
        match uu____5373 with
        | (tm_sz,uu____5381) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5391 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5391 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5399 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5399);
                   t_decls) in
            let uu____5400 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5420::(sz_arg,uu____5422)::uu____5423::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5472 =
                    let uu____5475 = FStar_List.tail args_e in
                    FStar_List.tail uu____5475 in
                  let uu____5478 =
                    let uu____5481 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5481 in
                  (uu____5472, uu____5478)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5487::(sz_arg,uu____5489)::uu____5490::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5539 =
                    let uu____5540 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5540 in
                  failwith uu____5539
              | uu____5549 ->
                  let uu____5556 = FStar_List.tail args_e in
                  (uu____5556, FStar_Pervasives_Native.None) in
            (match uu____5400 with
             | (arg_tms,ext_sz) ->
                 let uu____5579 = encode_args arg_tms env in
                 (match uu____5579 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5600 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5609 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5609 in
                      let unary_arith arg_tms2 =
                        let uu____5618 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5618 in
                      let binary arg_tms2 =
                        let uu____5631 =
                          let uu____5632 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5632 in
                        let uu____5633 =
                          let uu____5634 =
                            let uu____5635 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5635 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5634 in
                        (uu____5631, uu____5633) in
                      let binary_arith arg_tms2 =
                        let uu____5650 =
                          let uu____5651 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5651 in
                        let uu____5652 =
                          let uu____5653 =
                            let uu____5654 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5654 in
                          FStar_SMTEncoding_Term.unboxInt uu____5653 in
                        (uu____5650, uu____5652) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5703 =
                          let uu____5704 = mk_args ts in op uu____5704 in
                        FStar_All.pipe_right uu____5703 resBox in
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
                        let uu____5812 =
                          let uu____5815 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5815 in
                        let uu____5817 =
                          let uu____5820 =
                            let uu____5821 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5821 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5820 in
                        mk_bv uu____5812 unary uu____5817 arg_tms2 in
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
                      let uu____6020 =
                        let uu____6029 =
                          FStar_List.tryFind
                            (fun uu____6051  ->
                               match uu____6051 with
                               | (l,uu____6061) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6029 FStar_Util.must in
                      (match uu____6020 with
                       | (uu____6102,op) ->
                           let uu____6112 = op arg_tms1 in
                           (uu____6112, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6123 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6123
       then
         let uu____6124 = FStar_Syntax_Print.tag_of_term t in
         let uu____6125 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6126 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6124 uu____6125
           uu____6126
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6132 ->
           let uu____6157 =
             let uu____6158 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6159 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6160 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6161 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6158
               uu____6159 uu____6160 uu____6161 in
           failwith uu____6157
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6166 =
             let uu____6167 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6168 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6169 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6170 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6167
               uu____6168 uu____6169 uu____6170 in
           failwith uu____6166
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6176 =
             let uu____6177 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6177 in
           failwith uu____6176
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6184) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6225;
              FStar_Syntax_Syntax.vars = uu____6226;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6243 = varops.fresh "t" in
             (uu____6243, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6246 =
               let uu____6257 =
                 let uu____6260 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6260 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6257) in
             FStar_SMTEncoding_Term.DeclFun uu____6246 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6268) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6278 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6278, [])
       | FStar_Syntax_Syntax.Tm_type uu____6281 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6285) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6310 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6310 with
            | (binders1,res) ->
                let uu____6321 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6321
                then
                  let uu____6326 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6326 with
                   | (vars,guards,env',decls,uu____6351) ->
                       let fsym =
                         let uu____6369 = varops.fresh "f" in
                         (uu____6369, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6372 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___164_6381 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___164_6381.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___164_6381.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___164_6381.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___164_6381.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___164_6381.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___164_6381.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___164_6381.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___164_6381.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___164_6381.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___164_6381.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___164_6381.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___164_6381.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___164_6381.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___164_6381.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___164_6381.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___164_6381.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___164_6381.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___164_6381.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___164_6381.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___164_6381.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___164_6381.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___164_6381.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___164_6381.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___164_6381.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___164_6381.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___164_6381.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___164_6381.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___164_6381.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___164_6381.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___164_6381.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___164_6381.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___164_6381.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6372 with
                        | (pre_opt,res_t) ->
                            let uu____6392 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6392 with
                             | (res_pred,decls') ->
                                 let uu____6403 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6416 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6416, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6420 =
                                         encode_formula pre env' in
                                       (match uu____6420 with
                                        | (guard,decls0) ->
                                            let uu____6433 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6433, decls0)) in
                                 (match uu____6403 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6445 =
                                          let uu____6456 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6456) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6445 in
                                      let cvars =
                                        let uu____6474 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6474
                                          (FStar_List.filter
                                             (fun uu____6488  ->
                                                match uu____6488 with
                                                | (x,uu____6494) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6513 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6513 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6521 =
                                             let uu____6522 =
                                               let uu____6529 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6529) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6522 in
                                           (uu____6521,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6549 =
                                               let uu____6550 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6550 in
                                             varops.mk_unique uu____6549 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6561 =
                                               FStar_Options.log_queries () in
                                             if uu____6561
                                             then
                                               let uu____6564 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6564
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6572 =
                                               let uu____6579 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6579) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6572 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6591 =
                                               let uu____6598 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6598,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6591 in
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
                                             let uu____6619 =
                                               let uu____6626 =
                                                 let uu____6627 =
                                                   let uu____6638 =
                                                     let uu____6639 =
                                                       let uu____6644 =
                                                         let uu____6645 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6645 in
                                                       (f_has_t, uu____6644) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6639 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6638) in
                                                 mkForall_fuel uu____6627 in
                                               (uu____6626,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6619 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6668 =
                                               let uu____6675 =
                                                 let uu____6676 =
                                                   let uu____6687 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6687) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6676 in
                                               (uu____6675,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6668 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6712 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6712);
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
                     let uu____6727 =
                       let uu____6734 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6734,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6727 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6746 =
                       let uu____6753 =
                         let uu____6754 =
                           let uu____6765 =
                             let uu____6766 =
                               let uu____6771 =
                                 let uu____6772 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6772 in
                               (f_has_t, uu____6771) in
                             FStar_SMTEncoding_Util.mkImp uu____6766 in
                           ([[f_has_t]], [fsym], uu____6765) in
                         mkForall_fuel uu____6754 in
                       (uu____6753, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6746 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6799 ->
           let uu____6806 =
             let uu____6811 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6811 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6818;
                 FStar_Syntax_Syntax.vars = uu____6819;_} ->
                 let uu____6826 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6826 with
                  | (b,f1) ->
                      let uu____6851 =
                        let uu____6852 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6852 in
                      (uu____6851, f1))
             | uu____6861 -> failwith "impossible" in
           (match uu____6806 with
            | (x,f) ->
                let uu____6872 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6872 with
                 | (base_t,decls) ->
                     let uu____6883 = gen_term_var env x in
                     (match uu____6883 with
                      | (x1,xtm,env') ->
                          let uu____6897 = encode_formula f env' in
                          (match uu____6897 with
                           | (refinement,decls') ->
                               let uu____6908 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6908 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6924 =
                                        let uu____6927 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6934 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6927
                                          uu____6934 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6924 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6967  ->
                                              match uu____6967 with
                                              | (y,uu____6973) ->
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
                                    let uu____7006 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7006 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7014 =
                                           let uu____7015 =
                                             let uu____7022 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7022) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7015 in
                                         (uu____7014,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7043 =
                                             let uu____7044 =
                                               let uu____7045 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7045 in
                                             Prims.strcat module_name
                                               uu____7044 in
                                           varops.mk_unique uu____7043 in
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
                                           let uu____7059 =
                                             let uu____7066 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7066) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7059 in
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
                                           let uu____7081 =
                                             let uu____7088 =
                                               let uu____7089 =
                                                 let uu____7100 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7100) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7089 in
                                             (uu____7088,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7081 in
                                         let t_kinding =
                                           let uu____7118 =
                                             let uu____7125 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7125,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7118 in
                                         let t_interp =
                                           let uu____7143 =
                                             let uu____7150 =
                                               let uu____7151 =
                                                 let uu____7162 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7162) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7151 in
                                             let uu____7185 =
                                               let uu____7188 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7188 in
                                             (uu____7150, uu____7185,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7143 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7195 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7195);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7225 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7225 in
           let uu____7226 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7226 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7238 =
                    let uu____7245 =
                      let uu____7246 =
                        let uu____7247 =
                          let uu____7248 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7248 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7247 in
                      varops.mk_unique uu____7246 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7245) in
                  FStar_SMTEncoding_Util.mkAssume uu____7238 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7253 ->
           let uu____7268 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7268 with
            | (head1,args_e) ->
                let uu____7309 =
                  let uu____7322 =
                    let uu____7323 = FStar_Syntax_Subst.compress head1 in
                    uu____7323.FStar_Syntax_Syntax.n in
                  (uu____7322, args_e) in
                (match uu____7309 with
                 | uu____7338 when head_redex env head1 ->
                     let uu____7351 = whnf env t in
                     encode_term uu____7351 env
                 | uu____7352 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7371 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7385;
                       FStar_Syntax_Syntax.vars = uu____7386;_},uu____7387),uu____7388::
                    (v1,uu____7390)::(v2,uu____7392)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7443 = encode_term v1 env in
                     (match uu____7443 with
                      | (v11,decls1) ->
                          let uu____7454 = encode_term v2 env in
                          (match uu____7454 with
                           | (v21,decls2) ->
                               let uu____7465 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7465,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7469::(v1,uu____7471)::(v2,uu____7473)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7520 = encode_term v1 env in
                     (match uu____7520 with
                      | (v11,decls1) ->
                          let uu____7531 = encode_term v2 env in
                          (match uu____7531 with
                           | (v21,decls2) ->
                               let uu____7542 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7542,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7546)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7572)::(arg,uu____7574)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7609) ->
                     let e0 =
                       let uu____7627 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7627 in
                     ((let uu____7635 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7635
                       then
                         let uu____7636 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7636
                       else ());
                      (let e =
                         let uu____7641 =
                           let uu____7642 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7643 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7642
                             uu____7643 in
                         uu____7641 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7652),(arg,uu____7654)::[]) -> encode_term arg env
                 | uu____7679 ->
                     let uu____7692 = encode_args args_e env in
                     (match uu____7692 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7747 = encode_term head1 env in
                            match uu____7747 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7811 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7811 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7889  ->
                                                 fun uu____7890  ->
                                                   match (uu____7889,
                                                           uu____7890)
                                                   with
                                                   | ((bv,uu____7912),
                                                      (a,uu____7914)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7932 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7932
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7937 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7937 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7952 =
                                                   let uu____7959 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7968 =
                                                     let uu____7969 =
                                                       let uu____7970 =
                                                         let uu____7971 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7971 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7970 in
                                                     varops.mk_unique
                                                       uu____7969 in
                                                   (uu____7959,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7968) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7952 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7988 = lookup_free_var_sym env fv in
                            match uu____7988 with
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
                                   FStar_Syntax_Syntax.pos = uu____8019;
                                   FStar_Syntax_Syntax.vars = uu____8020;_},uu____8021)
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
                                   FStar_Syntax_Syntax.pos = uu____8032;
                                   FStar_Syntax_Syntax.vars = uu____8033;_},uu____8034)
                                ->
                                let uu____8039 =
                                  let uu____8040 =
                                    let uu____8045 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8045
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8040
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8039
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8075 =
                                  let uu____8076 =
                                    let uu____8081 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8081
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8076
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8075
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8110,(FStar_Util.Inl t1,uu____8112),uu____8113)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8162,(FStar_Util.Inr c,uu____8164),uu____8165)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8214 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8241 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8241 in
                               let uu____8242 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8242 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8258;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8259;_},uu____8260)
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
                                     | uu____8274 ->
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
           let uu____8323 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8323 with
            | (bs1,body1,opening) ->
                let fallback uu____8346 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8353 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8353, [decl]) in
                let is_impure rc =
                  let uu____8360 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8360 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8370 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8370
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8390 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8390
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8394 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8394)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8401 =
                         let uu____8402 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8402 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8401);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8404 =
                       (is_impure rc) &&
                         (let uu____8406 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8406) in
                     if uu____8404
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8413 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8413 with
                        | (vars,guards,envbody,decls,uu____8438) ->
                            let body2 =
                              let uu____8452 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8452
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8454 = encode_term body2 envbody in
                            (match uu____8454 with
                             | (body3,decls') ->
                                 let uu____8465 =
                                   let uu____8474 = codomain_eff rc in
                                   match uu____8474 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8493 = encode_term tfun env in
                                       (match uu____8493 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8465 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8525 =
                                          let uu____8536 =
                                            let uu____8537 =
                                              let uu____8542 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8542, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8537 in
                                          ([], vars, uu____8536) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8525 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8554 =
                                              let uu____8557 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8557
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8554 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8576 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8576 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8584 =
                                             let uu____8585 =
                                               let uu____8592 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8592) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8585 in
                                           (uu____8584,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8603 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8603 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8614 =
                                                    let uu____8615 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8615 = cache_size in
                                                  if uu____8614
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
                                                    let uu____8631 =
                                                      let uu____8632 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8632 in
                                                    varops.mk_unique
                                                      uu____8631 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8639 =
                                                    let uu____8646 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8646) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8639 in
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
                                                      let uu____8664 =
                                                        let uu____8665 =
                                                          let uu____8672 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8672,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8665 in
                                                      [uu____8664] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8685 =
                                                    let uu____8692 =
                                                      let uu____8693 =
                                                        let uu____8704 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8704) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8693 in
                                                    (uu____8692,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8685 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8721 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8721);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8724,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8725;
                          FStar_Syntax_Syntax.lbunivs = uu____8726;
                          FStar_Syntax_Syntax.lbtyp = uu____8727;
                          FStar_Syntax_Syntax.lbeff = uu____8728;
                          FStar_Syntax_Syntax.lbdef = uu____8729;_}::uu____8730),uu____8731)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8757;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8759;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8780 ->
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
              let uu____8850 = encode_term e1 env in
              match uu____8850 with
              | (ee1,decls1) ->
                  let uu____8861 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8861 with
                   | (xs,e21) ->
                       let uu____8886 = FStar_List.hd xs in
                       (match uu____8886 with
                        | (x1,uu____8900) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8902 = encode_body e21 env' in
                            (match uu____8902 with
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
            let uu____8934 =
              let uu____8941 =
                let uu____8942 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8942 in
              gen_term_var env uu____8941 in
            match uu____8934 with
            | (scrsym,scr',env1) ->
                let uu____8950 = encode_term e env1 in
                (match uu____8950 with
                 | (scr,decls) ->
                     let uu____8961 =
                       let encode_branch b uu____8986 =
                         match uu____8986 with
                         | (else_case,decls1) ->
                             let uu____9005 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9005 with
                              | (p,w,br) ->
                                  let uu____9031 = encode_pat env1 p in
                                  (match uu____9031 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9068  ->
                                                   match uu____9068 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9075 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9097 =
                                               encode_term w1 env2 in
                                             (match uu____9097 with
                                              | (w2,decls2) ->
                                                  let uu____9110 =
                                                    let uu____9111 =
                                                      let uu____9116 =
                                                        let uu____9117 =
                                                          let uu____9122 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9122) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9117 in
                                                      (guard, uu____9116) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9111 in
                                                  (uu____9110, decls2)) in
                                       (match uu____9075 with
                                        | (guard1,decls2) ->
                                            let uu____9135 =
                                              encode_br br env2 in
                                            (match uu____9135 with
                                             | (br1,decls3) ->
                                                 let uu____9148 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9148,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8961 with
                      | (match_tm,decls1) ->
                          let uu____9167 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9167, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9207 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9207
       then
         let uu____9208 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9208
       else ());
      (let uu____9210 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9210 with
       | (vars,pat_term) ->
           let uu____9227 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9280  ->
                     fun v1  ->
                       match uu____9280 with
                       | (env1,vars1) ->
                           let uu____9332 = gen_term_var env1 v1 in
                           (match uu____9332 with
                            | (xx,uu____9354,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9227 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9433 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9434 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9435 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9443 = encode_const c env1 in
                      (match uu____9443 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9457::uu____9458 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9461 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9484 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9484 with
                        | (uu____9491,uu____9492::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9495 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9528  ->
                                  match uu____9528 with
                                  | (arg,uu____9536) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9542 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9542)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9569) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9600 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9623 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9667  ->
                                  match uu____9667 with
                                  | (arg,uu____9681) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9687 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9687)) in
                      FStar_All.pipe_right uu____9623 FStar_List.flatten in
                let pat_term1 uu____9715 = encode_term pat_term env1 in
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
      let uu____9725 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9763  ->
                fun uu____9764  ->
                  match (uu____9763, uu____9764) with
                  | ((tms,decls),(t,uu____9800)) ->
                      let uu____9821 = encode_term t env in
                      (match uu____9821 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9725 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9878 = FStar_Syntax_Util.list_elements e in
        match uu____9878 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9899 =
          let uu____9914 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9914 FStar_Syntax_Util.head_and_args in
        match uu____9899 with
        | (head1,args) ->
            let uu____9953 =
              let uu____9966 =
                let uu____9967 = FStar_Syntax_Util.un_uinst head1 in
                uu____9967.FStar_Syntax_Syntax.n in
              (uu____9966, args) in
            (match uu____9953 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9981,uu____9982)::(e,uu____9984)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10019 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10055 =
            let uu____10070 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10070 FStar_Syntax_Util.head_and_args in
          match uu____10055 with
          | (head1,args) ->
              let uu____10111 =
                let uu____10124 =
                  let uu____10125 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10125.FStar_Syntax_Syntax.n in
                (uu____10124, args) in
              (match uu____10111 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10142)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10169 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10191 = smt_pat_or1 t1 in
            (match uu____10191 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10207 = list_elements1 e in
                 FStar_All.pipe_right uu____10207
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10225 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10225
                           (FStar_List.map one_pat)))
             | uu____10236 ->
                 let uu____10241 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10241])
        | uu____10262 ->
            let uu____10265 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10265] in
      let uu____10286 =
        let uu____10305 =
          let uu____10306 = FStar_Syntax_Subst.compress t in
          uu____10306.FStar_Syntax_Syntax.n in
        match uu____10305 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10345 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10345 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10388;
                        FStar_Syntax_Syntax.effect_name = uu____10389;
                        FStar_Syntax_Syntax.result_typ = uu____10390;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10392)::(post,uu____10394)::(pats,uu____10396)::[];
                        FStar_Syntax_Syntax.flags = uu____10397;_}
                      ->
                      let uu____10438 = lemma_pats pats in
                      (binders1, pre, post, uu____10438)
                  | uu____10455 -> failwith "impos"))
        | uu____10474 -> failwith "Impos" in
      match uu____10286 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___165_10522 = env in
            {
              bindings = (uu___165_10522.bindings);
              depth = (uu___165_10522.depth);
              tcenv = (uu___165_10522.tcenv);
              warn = (uu___165_10522.warn);
              cache = (uu___165_10522.cache);
              nolabels = (uu___165_10522.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___165_10522.encode_non_total_function_typ);
              current_module_name = (uu___165_10522.current_module_name)
            } in
          let uu____10523 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10523 with
           | (vars,guards,env2,decls,uu____10548) ->
               let uu____10561 =
                 let uu____10574 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10618 =
                             let uu____10627 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10627
                               FStar_List.unzip in
                           match uu____10618 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10574 FStar_List.unzip in
               (match uu____10561 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___166_10739 = env2 in
                      {
                        bindings = (uu___166_10739.bindings);
                        depth = (uu___166_10739.depth);
                        tcenv = (uu___166_10739.tcenv);
                        warn = (uu___166_10739.warn);
                        cache = (uu___166_10739.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___166_10739.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___166_10739.encode_non_total_function_typ);
                        current_module_name =
                          (uu___166_10739.current_module_name)
                      } in
                    let uu____10740 =
                      let uu____10745 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10745 env3 in
                    (match uu____10740 with
                     | (pre1,decls'') ->
                         let uu____10752 =
                           let uu____10757 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10757 env3 in
                         (match uu____10752 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10767 =
                                let uu____10768 =
                                  let uu____10779 =
                                    let uu____10780 =
                                      let uu____10785 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10785, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10780 in
                                  (pats, vars, uu____10779) in
                                FStar_SMTEncoding_Util.mkForall uu____10768 in
                              (uu____10767, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10804 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10804
        then
          let uu____10805 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10806 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10805 uu____10806
        else () in
      let enc f r l =
        let uu____10839 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10867 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10867 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10839 with
        | (decls,args) ->
            let uu____10896 =
              let uu___167_10897 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___167_10897.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___167_10897.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10896, decls) in
      let const_op f r uu____10928 =
        let uu____10941 = f r in (uu____10941, []) in
      let un_op f l =
        let uu____10960 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10960 in
      let bin_op f uu___141_10976 =
        match uu___141_10976 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10987 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11021 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11044  ->
                 match uu____11044 with
                 | (t,uu____11058) ->
                     let uu____11059 = encode_formula t env in
                     (match uu____11059 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11021 with
        | (decls,phis) ->
            let uu____11088 =
              let uu___168_11089 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___168_11089.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___168_11089.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11088, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11150  ->
               match uu____11150 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11169) -> false
                    | uu____11170 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11185 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11185
        else
          (let uu____11199 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11199 r rf) in
      let mk_imp1 r uu___142_11224 =
        match uu___142_11224 with
        | (lhs,uu____11230)::(rhs,uu____11232)::[] ->
            let uu____11259 = encode_formula rhs env in
            (match uu____11259 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11274) ->
                      (l1, decls1)
                  | uu____11279 ->
                      let uu____11280 = encode_formula lhs env in
                      (match uu____11280 with
                       | (l2,decls2) ->
                           let uu____11291 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11291, (FStar_List.append decls1 decls2)))))
        | uu____11294 -> failwith "impossible" in
      let mk_ite r uu___143_11315 =
        match uu___143_11315 with
        | (guard,uu____11321)::(_then,uu____11323)::(_else,uu____11325)::[]
            ->
            let uu____11362 = encode_formula guard env in
            (match uu____11362 with
             | (g,decls1) ->
                 let uu____11373 = encode_formula _then env in
                 (match uu____11373 with
                  | (t,decls2) ->
                      let uu____11384 = encode_formula _else env in
                      (match uu____11384 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11398 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11423 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11423 in
      let connectives =
        let uu____11441 =
          let uu____11454 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11454) in
        let uu____11471 =
          let uu____11486 =
            let uu____11499 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11499) in
          let uu____11516 =
            let uu____11531 =
              let uu____11546 =
                let uu____11559 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11559) in
              let uu____11576 =
                let uu____11591 =
                  let uu____11606 =
                    let uu____11619 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11619) in
                  [uu____11606;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11591 in
              uu____11546 :: uu____11576 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11531 in
          uu____11486 :: uu____11516 in
        uu____11441 :: uu____11471 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11940 = encode_formula phi' env in
            (match uu____11940 with
             | (phi2,decls) ->
                 let uu____11951 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11951, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11952 ->
            let uu____11959 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11959 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11998 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11998 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12010;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12012;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12033 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12033 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12080::(x,uu____12082)::(t,uu____12084)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12131 = encode_term x env in
                 (match uu____12131 with
                  | (x1,decls) ->
                      let uu____12142 = encode_term t env in
                      (match uu____12142 with
                       | (t1,decls') ->
                           let uu____12153 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12153, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12158)::(msg,uu____12160)::(phi2,uu____12162)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12207 =
                   let uu____12212 =
                     let uu____12213 = FStar_Syntax_Subst.compress r in
                     uu____12213.FStar_Syntax_Syntax.n in
                   let uu____12216 =
                     let uu____12217 = FStar_Syntax_Subst.compress msg in
                     uu____12217.FStar_Syntax_Syntax.n in
                   (uu____12212, uu____12216) in
                 (match uu____12207 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12226))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12232 -> fallback phi2)
             | uu____12237 when head_redex env head2 ->
                 let uu____12250 = whnf env phi1 in
                 encode_formula uu____12250 env
             | uu____12251 ->
                 let uu____12264 = encode_term phi1 env in
                 (match uu____12264 with
                  | (tt,decls) ->
                      let uu____12275 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___169_12278 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___169_12278.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___169_12278.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12275, decls)))
        | uu____12279 ->
            let uu____12280 = encode_term phi1 env in
            (match uu____12280 with
             | (tt,decls) ->
                 let uu____12291 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___170_12294 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___170_12294.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___170_12294.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12291, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12330 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12330 with
        | (vars,guards,env2,decls,uu____12369) ->
            let uu____12382 =
              let uu____12395 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12443 =
                          let uu____12452 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12482  ->
                                    match uu____12482 with
                                    | (t,uu____12492) ->
                                        encode_term t
                                          (let uu___171_12494 = env2 in
                                           {
                                             bindings =
                                               (uu___171_12494.bindings);
                                             depth = (uu___171_12494.depth);
                                             tcenv = (uu___171_12494.tcenv);
                                             warn = (uu___171_12494.warn);
                                             cache = (uu___171_12494.cache);
                                             nolabels =
                                               (uu___171_12494.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___171_12494.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___171_12494.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12452 FStar_List.unzip in
                        match uu____12443 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12395 FStar_List.unzip in
            (match uu____12382 with
             | (pats,decls') ->
                 let uu____12593 = encode_formula body env2 in
                 (match uu____12593 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12625;
                             FStar_SMTEncoding_Term.rng = uu____12626;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12641 -> guards in
                      let uu____12646 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12646, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12706  ->
                   match uu____12706 with
                   | (x,uu____12712) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12720 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12732 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12732) uu____12720 tl1 in
             let uu____12735 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12762  ->
                       match uu____12762 with
                       | (b,uu____12768) ->
                           let uu____12769 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12769)) in
             (match uu____12735 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12775) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12789 =
                    let uu____12790 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12790 in
                  FStar_Errors.warn pos uu____12789) in
       let uu____12791 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12791 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12800 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12858  ->
                     match uu____12858 with
                     | (l,uu____12872) -> FStar_Ident.lid_equals op l)) in
           (match uu____12800 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12905,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12945 = encode_q_body env vars pats body in
             match uu____12945 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12990 =
                     let uu____13001 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13001) in
                   FStar_SMTEncoding_Term.mkForall uu____12990
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13020 = encode_q_body env vars pats body in
             match uu____13020 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13064 =
                   let uu____13065 =
                     let uu____13076 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13076) in
                   FStar_SMTEncoding_Term.mkExists uu____13065
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13064, decls))))
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
  let uu____13174 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13174 with
  | (asym,a) ->
      let uu____13181 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13181 with
       | (xsym,x) ->
           let uu____13188 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13188 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13232 =
                      let uu____13243 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13243, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13232 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13269 =
                      let uu____13276 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13276) in
                    FStar_SMTEncoding_Util.mkApp uu____13269 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13289 =
                    let uu____13292 =
                      let uu____13295 =
                        let uu____13298 =
                          let uu____13299 =
                            let uu____13306 =
                              let uu____13307 =
                                let uu____13318 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13318) in
                              FStar_SMTEncoding_Util.mkForall uu____13307 in
                            (uu____13306, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13299 in
                        let uu____13335 =
                          let uu____13338 =
                            let uu____13339 =
                              let uu____13346 =
                                let uu____13347 =
                                  let uu____13358 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13358) in
                                FStar_SMTEncoding_Util.mkForall uu____13347 in
                              (uu____13346,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13339 in
                          [uu____13338] in
                        uu____13298 :: uu____13335 in
                      xtok_decl :: uu____13295 in
                    xname_decl :: uu____13292 in
                  (xtok1, uu____13289) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13449 =
                    let uu____13462 =
                      let uu____13471 =
                        let uu____13472 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13472 in
                      quant axy uu____13471 in
                    (FStar_Parser_Const.op_Eq, uu____13462) in
                  let uu____13481 =
                    let uu____13496 =
                      let uu____13509 =
                        let uu____13518 =
                          let uu____13519 =
                            let uu____13520 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13520 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13519 in
                        quant axy uu____13518 in
                      (FStar_Parser_Const.op_notEq, uu____13509) in
                    let uu____13529 =
                      let uu____13544 =
                        let uu____13557 =
                          let uu____13566 =
                            let uu____13567 =
                              let uu____13568 =
                                let uu____13573 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13574 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13573, uu____13574) in
                              FStar_SMTEncoding_Util.mkLT uu____13568 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13567 in
                          quant xy uu____13566 in
                        (FStar_Parser_Const.op_LT, uu____13557) in
                      let uu____13583 =
                        let uu____13598 =
                          let uu____13611 =
                            let uu____13620 =
                              let uu____13621 =
                                let uu____13622 =
                                  let uu____13627 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13628 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13627, uu____13628) in
                                FStar_SMTEncoding_Util.mkLTE uu____13622 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13621 in
                            quant xy uu____13620 in
                          (FStar_Parser_Const.op_LTE, uu____13611) in
                        let uu____13637 =
                          let uu____13652 =
                            let uu____13665 =
                              let uu____13674 =
                                let uu____13675 =
                                  let uu____13676 =
                                    let uu____13681 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13682 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13681, uu____13682) in
                                  FStar_SMTEncoding_Util.mkGT uu____13676 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13675 in
                              quant xy uu____13674 in
                            (FStar_Parser_Const.op_GT, uu____13665) in
                          let uu____13691 =
                            let uu____13706 =
                              let uu____13719 =
                                let uu____13728 =
                                  let uu____13729 =
                                    let uu____13730 =
                                      let uu____13735 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13736 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13735, uu____13736) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13730 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13729 in
                                quant xy uu____13728 in
                              (FStar_Parser_Const.op_GTE, uu____13719) in
                            let uu____13745 =
                              let uu____13760 =
                                let uu____13773 =
                                  let uu____13782 =
                                    let uu____13783 =
                                      let uu____13784 =
                                        let uu____13789 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13790 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13789, uu____13790) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13784 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13783 in
                                  quant xy uu____13782 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13773) in
                              let uu____13799 =
                                let uu____13814 =
                                  let uu____13827 =
                                    let uu____13836 =
                                      let uu____13837 =
                                        let uu____13838 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13838 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13837 in
                                    quant qx uu____13836 in
                                  (FStar_Parser_Const.op_Minus, uu____13827) in
                                let uu____13847 =
                                  let uu____13862 =
                                    let uu____13875 =
                                      let uu____13884 =
                                        let uu____13885 =
                                          let uu____13886 =
                                            let uu____13891 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13892 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13891, uu____13892) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13886 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13885 in
                                      quant xy uu____13884 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13875) in
                                  let uu____13901 =
                                    let uu____13916 =
                                      let uu____13929 =
                                        let uu____13938 =
                                          let uu____13939 =
                                            let uu____13940 =
                                              let uu____13945 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13946 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13945, uu____13946) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13940 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13939 in
                                        quant xy uu____13938 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13929) in
                                    let uu____13955 =
                                      let uu____13970 =
                                        let uu____13983 =
                                          let uu____13992 =
                                            let uu____13993 =
                                              let uu____13994 =
                                                let uu____13999 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14000 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13999, uu____14000) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13994 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13993 in
                                          quant xy uu____13992 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13983) in
                                      let uu____14009 =
                                        let uu____14024 =
                                          let uu____14037 =
                                            let uu____14046 =
                                              let uu____14047 =
                                                let uu____14048 =
                                                  let uu____14053 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14054 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14053, uu____14054) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14048 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14047 in
                                            quant xy uu____14046 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14037) in
                                        let uu____14063 =
                                          let uu____14078 =
                                            let uu____14091 =
                                              let uu____14100 =
                                                let uu____14101 =
                                                  let uu____14102 =
                                                    let uu____14107 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14108 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14107,
                                                      uu____14108) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14102 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14101 in
                                              quant xy uu____14100 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14091) in
                                          let uu____14117 =
                                            let uu____14132 =
                                              let uu____14145 =
                                                let uu____14154 =
                                                  let uu____14155 =
                                                    let uu____14156 =
                                                      let uu____14161 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14162 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14161,
                                                        uu____14162) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14156 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14155 in
                                                quant xy uu____14154 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14145) in
                                            let uu____14171 =
                                              let uu____14186 =
                                                let uu____14199 =
                                                  let uu____14208 =
                                                    let uu____14209 =
                                                      let uu____14210 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14210 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14209 in
                                                  quant qx uu____14208 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14199) in
                                              [uu____14186] in
                                            uu____14132 :: uu____14171 in
                                          uu____14078 :: uu____14117 in
                                        uu____14024 :: uu____14063 in
                                      uu____13970 :: uu____14009 in
                                    uu____13916 :: uu____13955 in
                                  uu____13862 :: uu____13901 in
                                uu____13814 :: uu____13847 in
                              uu____13760 :: uu____13799 in
                            uu____13706 :: uu____13745 in
                          uu____13652 :: uu____13691 in
                        uu____13598 :: uu____13637 in
                      uu____13544 :: uu____13583 in
                    uu____13496 :: uu____13529 in
                  uu____13449 :: uu____13481 in
                let mk1 l v1 =
                  let uu____14424 =
                    let uu____14433 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14491  ->
                              match uu____14491 with
                              | (l',uu____14505) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14433
                      (FStar_Option.map
                         (fun uu____14565  ->
                            match uu____14565 with | (uu____14584,b) -> b v1)) in
                  FStar_All.pipe_right uu____14424 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14655  ->
                          match uu____14655 with
                          | (l',uu____14669) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14710 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14710 with
        | (xxsym,xx) ->
            let uu____14717 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14717 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14727 =
                   let uu____14734 =
                     let uu____14735 =
                       let uu____14746 =
                         let uu____14747 =
                           let uu____14752 =
                             let uu____14753 =
                               let uu____14758 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14758) in
                             FStar_SMTEncoding_Util.mkEq uu____14753 in
                           (xx_has_type, uu____14752) in
                         FStar_SMTEncoding_Util.mkImp uu____14747 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14746) in
                     FStar_SMTEncoding_Util.mkForall uu____14735 in
                   let uu____14783 =
                     let uu____14784 =
                       let uu____14785 =
                         let uu____14786 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14786 in
                       Prims.strcat module_name uu____14785 in
                     varops.mk_unique uu____14784 in
                   (uu____14734, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14783) in
                 FStar_SMTEncoding_Util.mkAssume uu____14727)
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
    let uu____14826 =
      let uu____14827 =
        let uu____14834 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14834, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14827 in
    let uu____14837 =
      let uu____14840 =
        let uu____14841 =
          let uu____14848 =
            let uu____14849 =
              let uu____14860 =
                let uu____14861 =
                  let uu____14866 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14866) in
                FStar_SMTEncoding_Util.mkImp uu____14861 in
              ([[typing_pred]], [xx], uu____14860) in
            mkForall_fuel uu____14849 in
          (uu____14848, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14841 in
      [uu____14840] in
    uu____14826 :: uu____14837 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14908 =
      let uu____14909 =
        let uu____14916 =
          let uu____14917 =
            let uu____14928 =
              let uu____14933 =
                let uu____14936 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14936] in
              [uu____14933] in
            let uu____14941 =
              let uu____14942 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14942 tt in
            (uu____14928, [bb], uu____14941) in
          FStar_SMTEncoding_Util.mkForall uu____14917 in
        (uu____14916, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14909 in
    let uu____14963 =
      let uu____14966 =
        let uu____14967 =
          let uu____14974 =
            let uu____14975 =
              let uu____14986 =
                let uu____14987 =
                  let uu____14992 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14992) in
                FStar_SMTEncoding_Util.mkImp uu____14987 in
              ([[typing_pred]], [xx], uu____14986) in
            mkForall_fuel uu____14975 in
          (uu____14974, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14967 in
      [uu____14966] in
    uu____14908 :: uu____14963 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15042 =
        let uu____15043 =
          let uu____15050 =
            let uu____15053 =
              let uu____15056 =
                let uu____15059 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15060 =
                  let uu____15063 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15063] in
                uu____15059 :: uu____15060 in
              tt :: uu____15056 in
            tt :: uu____15053 in
          ("Prims.Precedes", uu____15050) in
        FStar_SMTEncoding_Util.mkApp uu____15043 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15042 in
    let precedes_y_x =
      let uu____15067 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15067 in
    let uu____15070 =
      let uu____15071 =
        let uu____15078 =
          let uu____15079 =
            let uu____15090 =
              let uu____15095 =
                let uu____15098 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15098] in
              [uu____15095] in
            let uu____15103 =
              let uu____15104 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15104 tt in
            (uu____15090, [bb], uu____15103) in
          FStar_SMTEncoding_Util.mkForall uu____15079 in
        (uu____15078, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15071 in
    let uu____15125 =
      let uu____15128 =
        let uu____15129 =
          let uu____15136 =
            let uu____15137 =
              let uu____15148 =
                let uu____15149 =
                  let uu____15154 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15154) in
                FStar_SMTEncoding_Util.mkImp uu____15149 in
              ([[typing_pred]], [xx], uu____15148) in
            mkForall_fuel uu____15137 in
          (uu____15136, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15129 in
      let uu____15179 =
        let uu____15182 =
          let uu____15183 =
            let uu____15190 =
              let uu____15191 =
                let uu____15202 =
                  let uu____15203 =
                    let uu____15208 =
                      let uu____15209 =
                        let uu____15212 =
                          let uu____15215 =
                            let uu____15218 =
                              let uu____15219 =
                                let uu____15224 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15225 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15224, uu____15225) in
                              FStar_SMTEncoding_Util.mkGT uu____15219 in
                            let uu____15226 =
                              let uu____15229 =
                                let uu____15230 =
                                  let uu____15235 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15236 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15235, uu____15236) in
                                FStar_SMTEncoding_Util.mkGTE uu____15230 in
                              let uu____15237 =
                                let uu____15240 =
                                  let uu____15241 =
                                    let uu____15246 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15247 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15246, uu____15247) in
                                  FStar_SMTEncoding_Util.mkLT uu____15241 in
                                [uu____15240] in
                              uu____15229 :: uu____15237 in
                            uu____15218 :: uu____15226 in
                          typing_pred_y :: uu____15215 in
                        typing_pred :: uu____15212 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15209 in
                    (uu____15208, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15203 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15202) in
              mkForall_fuel uu____15191 in
            (uu____15190,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15183 in
        [uu____15182] in
      uu____15128 :: uu____15179 in
    uu____15070 :: uu____15125 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15293 =
      let uu____15294 =
        let uu____15301 =
          let uu____15302 =
            let uu____15313 =
              let uu____15318 =
                let uu____15321 = FStar_SMTEncoding_Term.boxString b in
                [uu____15321] in
              [uu____15318] in
            let uu____15326 =
              let uu____15327 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15327 tt in
            (uu____15313, [bb], uu____15326) in
          FStar_SMTEncoding_Util.mkForall uu____15302 in
        (uu____15301, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15294 in
    let uu____15348 =
      let uu____15351 =
        let uu____15352 =
          let uu____15359 =
            let uu____15360 =
              let uu____15371 =
                let uu____15372 =
                  let uu____15377 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15377) in
                FStar_SMTEncoding_Util.mkImp uu____15372 in
              ([[typing_pred]], [xx], uu____15371) in
            mkForall_fuel uu____15360 in
          (uu____15359, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15352 in
      [uu____15351] in
    uu____15293 :: uu____15348 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15430 =
      let uu____15431 =
        let uu____15438 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15438, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15431 in
    [uu____15430] in
  let mk_and_interp env conj uu____15450 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15475 =
      let uu____15476 =
        let uu____15483 =
          let uu____15484 =
            let uu____15495 =
              let uu____15496 =
                let uu____15501 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15501, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15496 in
            ([[l_and_a_b]], [aa; bb], uu____15495) in
          FStar_SMTEncoding_Util.mkForall uu____15484 in
        (uu____15483, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15476 in
    [uu____15475] in
  let mk_or_interp env disj uu____15539 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15564 =
      let uu____15565 =
        let uu____15572 =
          let uu____15573 =
            let uu____15584 =
              let uu____15585 =
                let uu____15590 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15590, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15585 in
            ([[l_or_a_b]], [aa; bb], uu____15584) in
          FStar_SMTEncoding_Util.mkForall uu____15573 in
        (uu____15572, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15565 in
    [uu____15564] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15653 =
      let uu____15654 =
        let uu____15661 =
          let uu____15662 =
            let uu____15673 =
              let uu____15674 =
                let uu____15679 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15679, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15674 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15673) in
          FStar_SMTEncoding_Util.mkForall uu____15662 in
        (uu____15661, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15654 in
    [uu____15653] in
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
    let uu____15752 =
      let uu____15753 =
        let uu____15760 =
          let uu____15761 =
            let uu____15772 =
              let uu____15773 =
                let uu____15778 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15778, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15773 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15772) in
          FStar_SMTEncoding_Util.mkForall uu____15761 in
        (uu____15760, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15753 in
    [uu____15752] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15849 =
      let uu____15850 =
        let uu____15857 =
          let uu____15858 =
            let uu____15869 =
              let uu____15870 =
                let uu____15875 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15875, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15870 in
            ([[l_imp_a_b]], [aa; bb], uu____15869) in
          FStar_SMTEncoding_Util.mkForall uu____15858 in
        (uu____15857, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15850 in
    [uu____15849] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15938 =
      let uu____15939 =
        let uu____15946 =
          let uu____15947 =
            let uu____15958 =
              let uu____15959 =
                let uu____15964 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15964, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15959 in
            ([[l_iff_a_b]], [aa; bb], uu____15958) in
          FStar_SMTEncoding_Util.mkForall uu____15947 in
        (uu____15946, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15939 in
    [uu____15938] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16016 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16016 in
    let uu____16019 =
      let uu____16020 =
        let uu____16027 =
          let uu____16028 =
            let uu____16039 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16039) in
          FStar_SMTEncoding_Util.mkForall uu____16028 in
        (uu____16027, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16020 in
    [uu____16019] in
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
      let uu____16099 =
        let uu____16106 =
          let uu____16109 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16109] in
        ("Valid", uu____16106) in
      FStar_SMTEncoding_Util.mkApp uu____16099 in
    let uu____16112 =
      let uu____16113 =
        let uu____16120 =
          let uu____16121 =
            let uu____16132 =
              let uu____16133 =
                let uu____16138 =
                  let uu____16139 =
                    let uu____16150 =
                      let uu____16155 =
                        let uu____16158 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16158] in
                      [uu____16155] in
                    let uu____16163 =
                      let uu____16164 =
                        let uu____16169 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16169, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16164 in
                    (uu____16150, [xx1], uu____16163) in
                  FStar_SMTEncoding_Util.mkForall uu____16139 in
                (uu____16138, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16133 in
            ([[l_forall_a_b]], [aa; bb], uu____16132) in
          FStar_SMTEncoding_Util.mkForall uu____16121 in
        (uu____16120, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16113 in
    [uu____16112] in
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
      let uu____16251 =
        let uu____16258 =
          let uu____16261 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16261] in
        ("Valid", uu____16258) in
      FStar_SMTEncoding_Util.mkApp uu____16251 in
    let uu____16264 =
      let uu____16265 =
        let uu____16272 =
          let uu____16273 =
            let uu____16284 =
              let uu____16285 =
                let uu____16290 =
                  let uu____16291 =
                    let uu____16302 =
                      let uu____16307 =
                        let uu____16310 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16310] in
                      [uu____16307] in
                    let uu____16315 =
                      let uu____16316 =
                        let uu____16321 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16321, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16316 in
                    (uu____16302, [xx1], uu____16315) in
                  FStar_SMTEncoding_Util.mkExists uu____16291 in
                (uu____16290, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16285 in
            ([[l_exists_a_b]], [aa; bb], uu____16284) in
          FStar_SMTEncoding_Util.mkForall uu____16273 in
        (uu____16272, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16265 in
    [uu____16264] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16381 =
      let uu____16382 =
        let uu____16389 =
          let uu____16390 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16390 range_ty in
        let uu____16391 = varops.mk_unique "typing_range_const" in
        (uu____16389, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16391) in
      FStar_SMTEncoding_Util.mkAssume uu____16382 in
    [uu____16381] in
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
        let uu____16425 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16425 x1 t in
      let uu____16426 =
        let uu____16437 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16437) in
      FStar_SMTEncoding_Util.mkForall uu____16426 in
    let uu____16460 =
      let uu____16461 =
        let uu____16468 =
          let uu____16469 =
            let uu____16480 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16480) in
          FStar_SMTEncoding_Util.mkForall uu____16469 in
        (uu____16468,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16461 in
    [uu____16460] in
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
          let uu____16804 =
            FStar_Util.find_opt
              (fun uu____16830  ->
                 match uu____16830 with
                 | (l,uu____16842) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16804 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16867,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16906 = encode_function_type_as_formula t env in
        match uu____16906 with
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
              let uu____16952 =
                ((let uu____16955 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16955) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16952
              then
                let uu____16962 = new_term_constant_and_tok_from_lid env lid in
                match uu____16962 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16981 =
                        let uu____16982 = FStar_Syntax_Subst.compress t_norm in
                        uu____16982.FStar_Syntax_Syntax.n in
                      match uu____16981 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16988) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17018  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17023 -> [] in
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
                (let uu____17037 = prims.is lid in
                 if uu____17037
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17045 = prims.mk lid vname in
                   match uu____17045 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17069 =
                      let uu____17080 = curried_arrow_formals_comp t_norm in
                      match uu____17080 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17098 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17098
                            then
                              let uu____17099 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___172_17102 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___172_17102.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___172_17102.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___172_17102.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___172_17102.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___172_17102.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___172_17102.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___172_17102.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___172_17102.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___172_17102.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___172_17102.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___172_17102.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___172_17102.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___172_17102.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___172_17102.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___172_17102.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___172_17102.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___172_17102.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___172_17102.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___172_17102.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___172_17102.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___172_17102.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___172_17102.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___172_17102.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___172_17102.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___172_17102.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___172_17102.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___172_17102.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___172_17102.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___172_17102.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___172_17102.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___172_17102.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___172_17102.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17099
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17114 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17114)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17069 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17159 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17159 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17180 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___144_17222  ->
                                       match uu___144_17222 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17226 =
                                             FStar_Util.prefix vars in
                                           (match uu____17226 with
                                            | (uu____17247,(xxsym,uu____17249))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17267 =
                                                  let uu____17268 =
                                                    let uu____17275 =
                                                      let uu____17276 =
                                                        let uu____17287 =
                                                          let uu____17288 =
                                                            let uu____17293 =
                                                              let uu____17294
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17294 in
                                                            (vapp,
                                                              uu____17293) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17288 in
                                                        ([[vapp]], vars,
                                                          uu____17287) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17276 in
                                                    (uu____17275,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17268 in
                                                [uu____17267])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17313 =
                                             FStar_Util.prefix vars in
                                           (match uu____17313 with
                                            | (uu____17334,(xxsym,uu____17336))
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
                                                let uu____17359 =
                                                  let uu____17360 =
                                                    let uu____17367 =
                                                      let uu____17368 =
                                                        let uu____17379 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17379) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17368 in
                                                    (uu____17367,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17360 in
                                                [uu____17359])
                                       | uu____17396 -> [])) in
                             let uu____17397 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17397 with
                              | (vars,guards,env',decls1,uu____17424) ->
                                  let uu____17437 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17446 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17446, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17448 =
                                          encode_formula p env' in
                                        (match uu____17448 with
                                         | (g,ds) ->
                                             let uu____17459 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17459,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17437 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17472 =
                                           let uu____17479 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17479) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17472 in
                                       let uu____17488 =
                                         let vname_decl =
                                           let uu____17496 =
                                             let uu____17507 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17517  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17507,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17496 in
                                         let uu____17526 =
                                           let env2 =
                                             let uu___173_17532 = env1 in
                                             {
                                               bindings =
                                                 (uu___173_17532.bindings);
                                               depth = (uu___173_17532.depth);
                                               tcenv = (uu___173_17532.tcenv);
                                               warn = (uu___173_17532.warn);
                                               cache = (uu___173_17532.cache);
                                               nolabels =
                                                 (uu___173_17532.nolabels);
                                               use_zfuel_name =
                                                 (uu___173_17532.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___173_17532.current_module_name)
                                             } in
                                           let uu____17533 =
                                             let uu____17534 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17534 in
                                           if uu____17533
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17526 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17549::uu____17550 ->
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
                                                     let uu____17590 =
                                                       let uu____17601 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17601) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17590 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17628 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17631 =
                                               match formals with
                                               | [] ->
                                                   let uu____17648 =
                                                     let uu____17649 =
                                                       let uu____17652 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17652 in
                                                     push_free_var env1 lid
                                                       vname uu____17649 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17648)
                                               | uu____17657 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17664 =
                                                       let uu____17671 =
                                                         let uu____17672 =
                                                           let uu____17683 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17683) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17672 in
                                                       (uu____17671,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17664 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17631 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17488 with
                                        | (decls2,env2) ->
                                            let uu____17726 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17734 =
                                                encode_term res_t1 env' in
                                              match uu____17734 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17747 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17747, decls) in
                                            (match uu____17726 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17758 =
                                                     let uu____17765 =
                                                       let uu____17766 =
                                                         let uu____17777 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17777) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17766 in
                                                     (uu____17765,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17758 in
                                                 let freshness =
                                                   let uu____17793 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17793
                                                   then
                                                     let uu____17798 =
                                                       let uu____17799 =
                                                         let uu____17810 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17821 =
                                                           varops.next_id () in
                                                         (vname, uu____17810,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17821) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17799 in
                                                     let uu____17824 =
                                                       let uu____17827 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17827] in
                                                     uu____17798 ::
                                                       uu____17824
                                                   else [] in
                                                 let g =
                                                   let uu____17832 =
                                                     let uu____17835 =
                                                       let uu____17838 =
                                                         let uu____17841 =
                                                           let uu____17844 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17844 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17841 in
                                                       FStar_List.append
                                                         decls3 uu____17838 in
                                                     FStar_List.append decls2
                                                       uu____17835 in
                                                   FStar_List.append decls11
                                                     uu____17832 in
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
          let uu____17879 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17879 with
          | FStar_Pervasives_Native.None  ->
              let uu____17916 = encode_free_var false env x t t_norm [] in
              (match uu____17916 with
               | (decls,env1) ->
                   let uu____17943 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17943 with
                    | (n1,x',uu____17970) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17991) ->
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
            let uu____18051 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18051 with
            | (decls,env1) ->
                let uu____18070 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18070
                then
                  let uu____18077 =
                    let uu____18080 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18080 in
                  (uu____18077, env1)
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
             (fun uu____18135  ->
                fun lb  ->
                  match uu____18135 with
                  | (decls,env1) ->
                      let uu____18155 =
                        let uu____18162 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18162
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18155 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18184 = FStar_Syntax_Util.head_and_args t in
    match uu____18184 with
    | (hd1,args) ->
        let uu____18221 =
          let uu____18222 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18222.FStar_Syntax_Syntax.n in
        (match uu____18221 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18226,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18245 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18270  ->
      fun quals  ->
        match uu____18270 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18346 = FStar_Util.first_N nbinders formals in
              match uu____18346 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18427  ->
                         fun uu____18428  ->
                           match (uu____18427, uu____18428) with
                           | ((formal,uu____18446),(binder,uu____18448)) ->
                               let uu____18457 =
                                 let uu____18464 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18464) in
                               FStar_Syntax_Syntax.NT uu____18457) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18472 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18503  ->
                              match uu____18503 with
                              | (x,i) ->
                                  let uu____18514 =
                                    let uu___174_18515 = x in
                                    let uu____18516 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___174_18515.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___174_18515.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18516
                                    } in
                                  (uu____18514, i))) in
                    FStar_All.pipe_right uu____18472
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18534 =
                      let uu____18535 = FStar_Syntax_Subst.compress body in
                      let uu____18536 =
                        let uu____18537 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18537 in
                      FStar_Syntax_Syntax.extend_app_n uu____18535
                        uu____18536 in
                    uu____18534 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18598 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18598
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___175_18601 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___175_18601.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___175_18601.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___175_18601.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___175_18601.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___175_18601.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___175_18601.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___175_18601.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___175_18601.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___175_18601.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___175_18601.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___175_18601.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___175_18601.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___175_18601.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___175_18601.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___175_18601.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___175_18601.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___175_18601.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___175_18601.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___175_18601.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___175_18601.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___175_18601.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___175_18601.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___175_18601.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___175_18601.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___175_18601.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___175_18601.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___175_18601.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___175_18601.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___175_18601.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___175_18601.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___175_18601.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___175_18601.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18634 = FStar_Syntax_Util.abs_formals e in
                match uu____18634 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18698::uu____18699 ->
                         let uu____18714 =
                           let uu____18715 =
                             let uu____18718 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18718 in
                           uu____18715.FStar_Syntax_Syntax.n in
                         (match uu____18714 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18761 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18761 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18803 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18803
                                   then
                                     let uu____18838 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18838 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18932  ->
                                                   fun uu____18933  ->
                                                     match (uu____18932,
                                                             uu____18933)
                                                     with
                                                     | ((x,uu____18951),
                                                        (b,uu____18953)) ->
                                                         let uu____18962 =
                                                           let uu____18969 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18969) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18962)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18971 =
                                            let uu____18992 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18992) in
                                          (uu____18971, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19060 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19060 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19149) ->
                              let uu____19154 =
                                let uu____19175 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19175 in
                              (uu____19154, true)
                          | uu____19240 when Prims.op_Negation norm1 ->
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
                          | uu____19242 ->
                              let uu____19243 =
                                let uu____19244 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19245 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19244
                                  uu____19245 in
                              failwith uu____19243)
                     | uu____19270 ->
                         let rec aux' t_norm2 =
                           let uu____19295 =
                             let uu____19296 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19296.FStar_Syntax_Syntax.n in
                           match uu____19295 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19337 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19337 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19365 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19365 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19445)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19450 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19506 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19506
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19518 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19612  ->
                            fun lb  ->
                              match uu____19612 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19707 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19707
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19710 =
                                      let uu____19725 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19725
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19710 with
                                    | (tok,decl,env2) ->
                                        let uu____19771 =
                                          let uu____19784 =
                                            let uu____19795 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19795, tok) in
                                          uu____19784 :: toks in
                                        (uu____19771, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19518 with
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
                        | uu____19978 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19986 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19986 vars)
                            else
                              (let uu____19988 =
                                 let uu____19995 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19995) in
                               FStar_SMTEncoding_Util.mkApp uu____19988) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20077;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20079;
                             FStar_Syntax_Syntax.lbeff = uu____20080;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20143 =
                              let uu____20150 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20150 with
                              | (tcenv',uu____20168,e_t) ->
                                  let uu____20174 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20185 -> failwith "Impossible" in
                                  (match uu____20174 with
                                   | (e1,t_norm1) ->
                                       ((let uu___178_20201 = env2 in
                                         {
                                           bindings =
                                             (uu___178_20201.bindings);
                                           depth = (uu___178_20201.depth);
                                           tcenv = tcenv';
                                           warn = (uu___178_20201.warn);
                                           cache = (uu___178_20201.cache);
                                           nolabels =
                                             (uu___178_20201.nolabels);
                                           use_zfuel_name =
                                             (uu___178_20201.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___178_20201.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___178_20201.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20143 with
                             | (env',e1,t_norm1) ->
                                 let uu____20211 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20211 with
                                  | ((binders,body,uu____20232,uu____20233),curry)
                                      ->
                                      ((let uu____20244 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20244
                                        then
                                          let uu____20245 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20246 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20245 uu____20246
                                        else ());
                                       (let uu____20248 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20248 with
                                        | (vars,guards,env'1,binder_decls,uu____20275)
                                            ->
                                            let body1 =
                                              let uu____20289 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20289
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20292 =
                                              let uu____20301 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20301
                                              then
                                                let uu____20312 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20313 =
                                                  encode_formula body1 env'1 in
                                                (uu____20312, uu____20313)
                                              else
                                                (let uu____20323 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20323)) in
                                            (match uu____20292 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20346 =
                                                     let uu____20353 =
                                                       let uu____20354 =
                                                         let uu____20365 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20365) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20354 in
                                                     let uu____20376 =
                                                       let uu____20379 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20379 in
                                                     (uu____20353,
                                                       uu____20376,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20346 in
                                                 let uu____20382 =
                                                   let uu____20385 =
                                                     let uu____20388 =
                                                       let uu____20391 =
                                                         let uu____20394 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20394 in
                                                       FStar_List.append
                                                         decls2 uu____20391 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20388 in
                                                   FStar_List.append decls1
                                                     uu____20385 in
                                                 (uu____20382, env2))))))
                        | uu____20399 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20484 = varops.fresh "fuel" in
                          (uu____20484, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20487 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20575  ->
                                  fun uu____20576  ->
                                    match (uu____20575, uu____20576) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20724 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20724 in
                                        let gtok =
                                          let uu____20726 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20726 in
                                        let env4 =
                                          let uu____20728 =
                                            let uu____20731 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20731 in
                                          push_free_var env3 flid gtok
                                            uu____20728 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20487 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20887 t_norm
                              uu____20889 =
                              match (uu____20887, uu____20889) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20933;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20934;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20962 =
                                    let uu____20969 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20969 with
                                    | (tcenv',uu____20991,e_t) ->
                                        let uu____20997 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21008 ->
                                              failwith "Impossible" in
                                        (match uu____20997 with
                                         | (e1,t_norm1) ->
                                             ((let uu___179_21024 = env3 in
                                               {
                                                 bindings =
                                                   (uu___179_21024.bindings);
                                                 depth =
                                                   (uu___179_21024.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___179_21024.warn);
                                                 cache =
                                                   (uu___179_21024.cache);
                                                 nolabels =
                                                   (uu___179_21024.nolabels);
                                                 use_zfuel_name =
                                                   (uu___179_21024.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___179_21024.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___179_21024.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20962 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21039 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____21039
                                         then
                                           let uu____21040 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____21041 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____21042 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21040 uu____21041
                                             uu____21042
                                         else ());
                                        (let uu____21044 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21044 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21081 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21081
                                               then
                                                 let uu____21082 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21083 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21084 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21085 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21082 uu____21083
                                                   uu____21084 uu____21085
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21089 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21089 with
                                               | (vars,guards,env'1,binder_decls,uu____21120)
                                                   ->
                                                   let decl_g =
                                                     let uu____21134 =
                                                       let uu____21145 =
                                                         let uu____21148 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21148 in
                                                       (g, uu____21145,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21134 in
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
                                                     let uu____21173 =
                                                       let uu____21180 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21180) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21173 in
                                                   let gsapp =
                                                     let uu____21190 =
                                                       let uu____21197 =
                                                         let uu____21200 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21200 ::
                                                           vars_tm in
                                                       (g, uu____21197) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21190 in
                                                   let gmax =
                                                     let uu____21206 =
                                                       let uu____21213 =
                                                         let uu____21216 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21216 ::
                                                           vars_tm in
                                                       (g, uu____21213) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21206 in
                                                   let body1 =
                                                     let uu____21222 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21222
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21224 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21224 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21242 =
                                                            let uu____21249 =
                                                              let uu____21250
                                                                =
                                                                let uu____21265
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
                                                                  uu____21265) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21250 in
                                                            let uu____21286 =
                                                              let uu____21289
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21289 in
                                                            (uu____21249,
                                                              uu____21286,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21242 in
                                                        let eqn_f =
                                                          let uu____21293 =
                                                            let uu____21300 =
                                                              let uu____21301
                                                                =
                                                                let uu____21312
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21312) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21301 in
                                                            (uu____21300,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21293 in
                                                        let eqn_g' =
                                                          let uu____21326 =
                                                            let uu____21333 =
                                                              let uu____21334
                                                                =
                                                                let uu____21345
                                                                  =
                                                                  let uu____21346
                                                                    =
                                                                    let uu____21351
                                                                    =
                                                                    let uu____21352
                                                                    =
                                                                    let uu____21359
                                                                    =
                                                                    let uu____21362
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21362
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21359) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21352 in
                                                                    (gsapp,
                                                                    uu____21351) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21346 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21345) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21334 in
                                                            (uu____21333,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21326 in
                                                        let uu____21385 =
                                                          let uu____21394 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21394
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21423)
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
                                                                  let uu____21448
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21448
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21453
                                                                  =
                                                                  let uu____21460
                                                                    =
                                                                    let uu____21461
                                                                    =
                                                                    let uu____21472
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21472) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21461 in
                                                                  (uu____21460,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21453 in
                                                              let uu____21493
                                                                =
                                                                let uu____21500
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21500
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21513
                                                                    =
                                                                    let uu____21516
                                                                    =
                                                                    let uu____21517
                                                                    =
                                                                    let uu____21524
                                                                    =
                                                                    let uu____21525
                                                                    =
                                                                    let uu____21536
                                                                    =
                                                                    let uu____21537
                                                                    =
                                                                    let uu____21542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21542,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21537 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21536) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21525 in
                                                                    (uu____21524,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21517 in
                                                                    [uu____21516] in
                                                                    (d3,
                                                                    uu____21513) in
                                                              (match uu____21493
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21385
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
                            let uu____21607 =
                              let uu____21620 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21699  ->
                                   fun uu____21700  ->
                                     match (uu____21699, uu____21700) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21855 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21855 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21620 in
                            (match uu____21607 with
                             | (decls2,eqns,env01) ->
                                 let uu____21928 =
                                   let isDeclFun uu___145_21940 =
                                     match uu___145_21940 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21941 -> true
                                     | uu____21952 -> false in
                                   let uu____21953 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21953
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21928 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21993 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___146_21997  ->
                                 match uu___146_21997 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21998 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22004 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22004))) in
                      if uu____21993
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
                   let uu____22056 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22056
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
        let uu____22105 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22105 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22109 = encode_sigelt' env se in
      match uu____22109 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22125 =
                  let uu____22126 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22126 in
                [uu____22125]
            | uu____22127 ->
                let uu____22128 =
                  let uu____22131 =
                    let uu____22132 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22132 in
                  uu____22131 :: g in
                let uu____22133 =
                  let uu____22136 =
                    let uu____22137 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22137 in
                  [uu____22136] in
                FStar_List.append uu____22128 uu____22133 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22150 =
          let uu____22151 = FStar_Syntax_Subst.compress t in
          uu____22151.FStar_Syntax_Syntax.n in
        match uu____22150 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22155)) -> s = "opaque_to_smt"
        | uu____22156 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22161 =
          let uu____22162 = FStar_Syntax_Subst.compress t in
          uu____22162.FStar_Syntax_Syntax.n in
        match uu____22161 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22166)) -> s = "uninterpreted_by_smt"
        | uu____22167 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22172 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22177 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22180 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22183 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22198 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22202 =
            let uu____22203 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22203 Prims.op_Negation in
          if uu____22202
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22229 ->
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
               let uu____22249 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22249 with
               | (aname,atok,env2) ->
                   let uu____22265 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22265 with
                    | (formals,uu____22283) ->
                        let uu____22296 =
                          let uu____22301 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22301 env2 in
                        (match uu____22296 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22313 =
                                 let uu____22314 =
                                   let uu____22325 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22341  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22325,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22314 in
                               [uu____22313;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22354 =
                               let aux uu____22406 uu____22407 =
                                 match (uu____22406, uu____22407) with
                                 | ((bv,uu____22459),(env3,acc_sorts,acc)) ->
                                     let uu____22497 = gen_term_var env3 bv in
                                     (match uu____22497 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22354 with
                              | (uu____22569,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22592 =
                                      let uu____22599 =
                                        let uu____22600 =
                                          let uu____22611 =
                                            let uu____22612 =
                                              let uu____22617 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22617) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22612 in
                                          ([[app]], xs_sorts, uu____22611) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22600 in
                                      (uu____22599,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22592 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22637 =
                                      let uu____22644 =
                                        let uu____22645 =
                                          let uu____22656 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22656) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22645 in
                                      (uu____22644,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22637 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22675 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22675 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22703,uu____22704)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22705 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22705 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22722,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22728 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___147_22732  ->
                      match uu___147_22732 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22733 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22738 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22739 -> false)) in
            Prims.op_Negation uu____22728 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22748 =
               let uu____22755 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22755 env fv t quals in
             match uu____22748 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22770 =
                   let uu____22773 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22773 in
                 (uu____22770, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22781 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22781 with
           | (uu____22790,f1) ->
               let uu____22792 = encode_formula f1 env in
               (match uu____22792 with
                | (f2,decls) ->
                    let g =
                      let uu____22806 =
                        let uu____22807 =
                          let uu____22814 =
                            let uu____22817 =
                              let uu____22818 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22818 in
                            FStar_Pervasives_Native.Some uu____22817 in
                          let uu____22819 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22814, uu____22819) in
                        FStar_SMTEncoding_Util.mkAssume uu____22807 in
                      [uu____22806] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22825) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22837 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22855 =
                       let uu____22858 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22858.FStar_Syntax_Syntax.fv_name in
                     uu____22855.FStar_Syntax_Syntax.v in
                   let uu____22859 =
                     let uu____22860 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22860 in
                   if uu____22859
                   then
                     let val_decl =
                       let uu___182_22888 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___182_22888.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___182_22888.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___182_22888.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22893 = encode_sigelt' env1 val_decl in
                     match uu____22893 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22837 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22921,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22923;
                          FStar_Syntax_Syntax.lbtyp = uu____22924;
                          FStar_Syntax_Syntax.lbeff = uu____22925;
                          FStar_Syntax_Syntax.lbdef = uu____22926;_}::[]),uu____22927)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22946 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22946 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22975 =
                   let uu____22978 =
                     let uu____22979 =
                       let uu____22986 =
                         let uu____22987 =
                           let uu____22998 =
                             let uu____22999 =
                               let uu____23004 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23004) in
                             FStar_SMTEncoding_Util.mkEq uu____22999 in
                           ([[b2t_x]], [xx], uu____22998) in
                         FStar_SMTEncoding_Util.mkForall uu____22987 in
                       (uu____22986,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22979 in
                   [uu____22978] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22975 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23037,uu____23038) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___148_23047  ->
                  match uu___148_23047 with
                  | FStar_Syntax_Syntax.Discriminator uu____23048 -> true
                  | uu____23049 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23052,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23063 =
                     let uu____23064 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23064.FStar_Ident.idText in
                   uu____23063 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___149_23068  ->
                     match uu___149_23068 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23069 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23073) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___150_23090  ->
                  match uu___150_23090 with
                  | FStar_Syntax_Syntax.Projector uu____23091 -> true
                  | uu____23096 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23099 = try_lookup_free_var env l in
          (match uu____23099 with
           | FStar_Pervasives_Native.Some uu____23106 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___183_23110 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___183_23110.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___183_23110.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___183_23110.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23117) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23135) ->
          let uu____23144 = encode_sigelts env ses in
          (match uu____23144 with
           | (g,env1) ->
               let uu____23161 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___151_23184  ->
                         match uu___151_23184 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23185;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23186;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23187;_}
                             -> false
                         | uu____23190 -> true)) in
               (match uu____23161 with
                | (g',inversions) ->
                    let uu____23205 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___152_23226  ->
                              match uu___152_23226 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23227 ->
                                  true
                              | uu____23238 -> false)) in
                    (match uu____23205 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23256,tps,k,uu____23259,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___153_23276  ->
                    match uu___153_23276 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23277 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23286 = c in
              match uu____23286 with
              | (name,args,uu____23291,uu____23292,uu____23293) ->
                  let uu____23298 =
                    let uu____23299 =
                      let uu____23310 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23327  ->
                                match uu____23327 with
                                | (uu____23334,sort,uu____23336) -> sort)) in
                      (name, uu____23310, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23299 in
                  [uu____23298]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23363 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23369 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23369 FStar_Option.isNone)) in
            if uu____23363
            then []
            else
              (let uu____23401 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23401 with
               | (xxsym,xx) ->
                   let uu____23410 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23449  ->
                             fun l  ->
                               match uu____23449 with
                               | (out,decls) ->
                                   let uu____23469 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23469 with
                                    | (uu____23480,data_t) ->
                                        let uu____23482 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23482 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23528 =
                                                 let uu____23529 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23529.FStar_Syntax_Syntax.n in
                                               match uu____23528 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23540,indices) ->
                                                   indices
                                               | uu____23562 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23586  ->
                                                         match uu____23586
                                                         with
                                                         | (x,uu____23592) ->
                                                             let uu____23593
                                                               =
                                                               let uu____23594
                                                                 =
                                                                 let uu____23601
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23601,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23594 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23593)
                                                    env) in
                                             let uu____23604 =
                                               encode_args indices env1 in
                                             (match uu____23604 with
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
                                                      let uu____23630 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23646
                                                                 =
                                                                 let uu____23651
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23651,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23646)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23630
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23654 =
                                                      let uu____23655 =
                                                        let uu____23660 =
                                                          let uu____23661 =
                                                            let uu____23666 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23666,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23661 in
                                                        (out, uu____23660) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23655 in
                                                    (uu____23654,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23410 with
                    | (data_ax,decls) ->
                        let uu____23679 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23679 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23690 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23690 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23694 =
                                 let uu____23701 =
                                   let uu____23702 =
                                     let uu____23713 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23728 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23713,
                                       uu____23728) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23702 in
                                 let uu____23743 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23701,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23743) in
                               FStar_SMTEncoding_Util.mkAssume uu____23694 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23746 =
            let uu____23759 =
              let uu____23760 = FStar_Syntax_Subst.compress k in
              uu____23760.FStar_Syntax_Syntax.n in
            match uu____23759 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23805 -> (tps, k) in
          (match uu____23746 with
           | (formals,res) ->
               let uu____23828 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23828 with
                | (formals1,res1) ->
                    let uu____23839 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23839 with
                     | (vars,guards,env',binder_decls,uu____23864) ->
                         let uu____23877 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23877 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23896 =
                                  let uu____23903 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23903) in
                                FStar_SMTEncoding_Util.mkApp uu____23896 in
                              let uu____23912 =
                                let tname_decl =
                                  let uu____23922 =
                                    let uu____23923 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23955  ->
                                              match uu____23955 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23968 = varops.next_id () in
                                    (tname, uu____23923,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23968, false) in
                                  constructor_or_logic_type_decl uu____23922 in
                                let uu____23977 =
                                  match vars with
                                  | [] ->
                                      let uu____23990 =
                                        let uu____23991 =
                                          let uu____23994 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23994 in
                                        push_free_var env1 t tname
                                          uu____23991 in
                                      ([], uu____23990)
                                  | uu____24001 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24010 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24010 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24024 =
                                          let uu____24031 =
                                            let uu____24032 =
                                              let uu____24047 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24047) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24032 in
                                          (uu____24031,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24024 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23977 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23912 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24087 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24087 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24105 =
                                               let uu____24106 =
                                                 let uu____24113 =
                                                   let uu____24114 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24114 in
                                                 (uu____24113,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24106 in
                                             [uu____24105]
                                           else [] in
                                         let uu____24118 =
                                           let uu____24121 =
                                             let uu____24124 =
                                               let uu____24125 =
                                                 let uu____24132 =
                                                   let uu____24133 =
                                                     let uu____24144 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24144) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24133 in
                                                 (uu____24132,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24125 in
                                             [uu____24124] in
                                           FStar_List.append karr uu____24121 in
                                         FStar_List.append decls1 uu____24118 in
                                   let aux =
                                     let uu____24160 =
                                       let uu____24163 =
                                         inversion_axioms tapp vars in
                                       let uu____24166 =
                                         let uu____24169 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24169] in
                                       FStar_List.append uu____24163
                                         uu____24166 in
                                     FStar_List.append kindingAx uu____24160 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24176,uu____24177,uu____24178,uu____24179,uu____24180)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24188,t,uu____24190,n_tps,uu____24192) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24200 = new_term_constant_and_tok_from_lid env d in
          (match uu____24200 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24217 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24217 with
                | (formals,t_res) ->
                    let uu____24252 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24252 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24266 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24266 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24336 =
                                            mk_term_projector_name d x in
                                          (uu____24336,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24338 =
                                  let uu____24357 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24357, true) in
                                FStar_All.pipe_right uu____24338
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
                              let uu____24396 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24396 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24408::uu____24409 ->
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
                                         let uu____24454 =
                                           let uu____24465 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24465) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24454
                                     | uu____24490 -> tok_typing in
                                   let uu____24499 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24499 with
                                    | (vars',guards',env'',decls_formals,uu____24524)
                                        ->
                                        let uu____24537 =
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
                                        (match uu____24537 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24568 ->
                                                   let uu____24575 =
                                                     let uu____24576 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24576 in
                                                   [uu____24575] in
                                             let encode_elim uu____24586 =
                                               let uu____24587 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24587 with
                                               | (head1,args) ->
                                                   let uu____24630 =
                                                     let uu____24631 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24631.FStar_Syntax_Syntax.n in
                                                   (match uu____24630 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24641;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24642;_},uu____24643)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24649 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24649
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
                                                                 | uu____24692
                                                                    ->
                                                                    let uu____24693
                                                                    =
                                                                    let uu____24694
                                                                    =
                                                                    let uu____24699
                                                                    =
                                                                    let uu____24700
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24700 in
                                                                    (uu____24699,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24694 in
                                                                    FStar_Exn.raise
                                                                    uu____24693 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24716
                                                                    =
                                                                    let uu____24717
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24717 in
                                                                    if
                                                                    uu____24716
                                                                    then
                                                                    let uu____24730
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24730]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24732
                                                               =
                                                               let uu____24745
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24795
                                                                     ->
                                                                    fun
                                                                    uu____24796
                                                                     ->
                                                                    match 
                                                                    (uu____24795,
                                                                    uu____24796)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24891
                                                                    =
                                                                    let uu____24898
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24898 in
                                                                    (match uu____24891
                                                                    with
                                                                    | 
                                                                    (uu____24911,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24919
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24919
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24921
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24921
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
                                                                 uu____24745 in
                                                             (match uu____24732
                                                              with
                                                              | (uu____24936,arg_vars,elim_eqns_or_guards,uu____24939)
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
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24976
                                                                    =
                                                                    let uu____24977
                                                                    =
                                                                    let uu____24988
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25000
                                                                    =
                                                                    let uu____25005
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25005) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25000 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24988,
                                                                    uu____24999) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24977 in
                                                                    (uu____24976,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24969 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25028
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25028,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25030
                                                                    =
                                                                    let uu____25037
                                                                    =
                                                                    let uu____25038
                                                                    =
                                                                    let uu____25049
                                                                    =
                                                                    let uu____25054
                                                                    =
                                                                    let uu____25057
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25057] in
                                                                    [uu____25054] in
                                                                    let uu____25062
                                                                    =
                                                                    let uu____25063
                                                                    =
                                                                    let uu____25068
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25069
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25068,
                                                                    uu____25069) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25063 in
                                                                    (uu____25049,
                                                                    [x],
                                                                    uu____25062) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25038 in
                                                                    let uu____25088
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25037,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25088) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25030
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25095
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
                                                                    (let uu____25123
                                                                    =
                                                                    let uu____25124
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25124
                                                                    dapp1 in
                                                                    [uu____25123]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25095
                                                                    FStar_List.flatten in
                                                                    let uu____25131
                                                                    =
                                                                    let uu____25138
                                                                    =
                                                                    let uu____25139
                                                                    =
                                                                    let uu____25150
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25161
                                                                    =
                                                                    let uu____25162
                                                                    =
                                                                    let uu____25167
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25167) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25162 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25150,
                                                                    uu____25161) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25139 in
                                                                    (uu____25138,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25131) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25188 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25188
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
                                                                 | uu____25231
                                                                    ->
                                                                    let uu____25232
                                                                    =
                                                                    let uu____25233
                                                                    =
                                                                    let uu____25238
                                                                    =
                                                                    let uu____25239
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25239 in
                                                                    (uu____25238,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25233 in
                                                                    FStar_Exn.raise
                                                                    uu____25232 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25255
                                                                    =
                                                                    let uu____25256
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25256 in
                                                                    if
                                                                    uu____25255
                                                                    then
                                                                    let uu____25269
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25269]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25271
                                                               =
                                                               let uu____25284
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25334
                                                                     ->
                                                                    fun
                                                                    uu____25335
                                                                     ->
                                                                    match 
                                                                    (uu____25334,
                                                                    uu____25335)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25430
                                                                    =
                                                                    let uu____25437
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25437 in
                                                                    (match uu____25430
                                                                    with
                                                                    | 
                                                                    (uu____25450,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25458
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25458
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25460
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25460
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
                                                                 uu____25284 in
                                                             (match uu____25271
                                                              with
                                                              | (uu____25475,arg_vars,elim_eqns_or_guards,uu____25478)
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
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25515
                                                                    =
                                                                    let uu____25516
                                                                    =
                                                                    let uu____25527
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25538
                                                                    =
                                                                    let uu____25539
                                                                    =
                                                                    let uu____25544
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25544) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25539 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25527,
                                                                    uu____25538) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25516 in
                                                                    (uu____25515,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25508 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25567
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25567,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25569
                                                                    =
                                                                    let uu____25576
                                                                    =
                                                                    let uu____25577
                                                                    =
                                                                    let uu____25588
                                                                    =
                                                                    let uu____25593
                                                                    =
                                                                    let uu____25596
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25596] in
                                                                    [uu____25593] in
                                                                    let uu____25601
                                                                    =
                                                                    let uu____25602
                                                                    =
                                                                    let uu____25607
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25608
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25607,
                                                                    uu____25608) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25602 in
                                                                    (uu____25588,
                                                                    [x],
                                                                    uu____25601) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25577 in
                                                                    let uu____25627
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25576,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25627) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25569
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25634
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
                                                                    (let uu____25662
                                                                    =
                                                                    let uu____25663
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25663
                                                                    dapp1 in
                                                                    [uu____25662]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25634
                                                                    FStar_List.flatten in
                                                                    let uu____25670
                                                                    =
                                                                    let uu____25677
                                                                    =
                                                                    let uu____25678
                                                                    =
                                                                    let uu____25689
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25700
                                                                    =
                                                                    let uu____25701
                                                                    =
                                                                    let uu____25706
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25706) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25701 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25689,
                                                                    uu____25700) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25678 in
                                                                    (uu____25677,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25670) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25725 ->
                                                        ((let uu____25727 =
                                                            let uu____25728 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25729 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25728
                                                              uu____25729 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25727);
                                                         ([], []))) in
                                             let uu____25734 = encode_elim () in
                                             (match uu____25734 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25754 =
                                                      let uu____25757 =
                                                        let uu____25760 =
                                                          let uu____25763 =
                                                            let uu____25766 =
                                                              let uu____25767
                                                                =
                                                                let uu____25778
                                                                  =
                                                                  let uu____25781
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25782 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25781 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25778) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25767 in
                                                            [uu____25766] in
                                                          let uu____25787 =
                                                            let uu____25790 =
                                                              let uu____25793
                                                                =
                                                                let uu____25796
                                                                  =
                                                                  let uu____25799
                                                                    =
                                                                    let uu____25802
                                                                    =
                                                                    let uu____25805
                                                                    =
                                                                    let uu____25806
                                                                    =
                                                                    let uu____25813
                                                                    =
                                                                    let uu____25814
                                                                    =
                                                                    let uu____25825
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25825) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25814 in
                                                                    (uu____25813,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25806 in
                                                                    let uu____25838
                                                                    =
                                                                    let uu____25841
                                                                    =
                                                                    let uu____25842
                                                                    =
                                                                    let uu____25849
                                                                    =
                                                                    let uu____25850
                                                                    =
                                                                    let uu____25861
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25872
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25861,
                                                                    uu____25872) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25850 in
                                                                    (uu____25849,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25842 in
                                                                    [uu____25841] in
                                                                    uu____25805
                                                                    ::
                                                                    uu____25838 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25802 in
                                                                  FStar_List.append
                                                                    uu____25799
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25796 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25793 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25790 in
                                                          FStar_List.append
                                                            uu____25763
                                                            uu____25787 in
                                                        FStar_List.append
                                                          decls3 uu____25760 in
                                                      FStar_List.append
                                                        decls2 uu____25757 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25754 in
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
           (fun uu____25918  ->
              fun se  ->
                match uu____25918 with
                | (g,env1) ->
                    let uu____25938 = encode_sigelt env1 se in
                    (match uu____25938 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25997 =
        match uu____25997 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26029 ->
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
                 ((let uu____26035 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26035
                   then
                     let uu____26036 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26037 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26038 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26036 uu____26037 uu____26038
                   else ());
                  (let uu____26040 = encode_term t1 env1 in
                   match uu____26040 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26056 =
                         let uu____26063 =
                           let uu____26064 =
                             let uu____26065 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26065
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26064 in
                         new_term_constant_from_string env1 x uu____26063 in
                       (match uu____26056 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26081 = FStar_Options.log_queries () in
                              if uu____26081
                              then
                                let uu____26084 =
                                  let uu____26085 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26086 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26087 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26085 uu____26086 uu____26087 in
                                FStar_Pervasives_Native.Some uu____26084
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26103,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26117 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26117 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26140,se,uu____26142) ->
                 let uu____26147 = encode_sigelt env1 se in
                 (match uu____26147 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26164,se) ->
                 let uu____26170 = encode_sigelt env1 se in
                 (match uu____26170 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26187 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26187 with | (uu____26210,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26225 'Auu____26226 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26226,'Auu____26225)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26294  ->
              match uu____26294 with
              | (l,uu____26306,uu____26307) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26353  ->
              match uu____26353 with
              | (l,uu____26367,uu____26368) ->
                  let uu____26377 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26378 =
                    let uu____26381 =
                      let uu____26382 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26382 in
                    [uu____26381] in
                  uu____26377 :: uu____26378)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26404 =
      let uu____26407 =
        let uu____26408 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26411 =
          let uu____26412 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26412 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26408;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26411
        } in
      [uu____26407] in
    FStar_ST.op_Colon_Equals last_env uu____26404
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26471 = FStar_ST.op_Bang last_env in
      match uu____26471 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26525 ->
          let uu___184_26528 = e in
          let uu____26529 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___184_26528.bindings);
            depth = (uu___184_26528.depth);
            tcenv;
            warn = (uu___184_26528.warn);
            cache = (uu___184_26528.cache);
            nolabels = (uu___184_26528.nolabels);
            use_zfuel_name = (uu___184_26528.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___184_26528.encode_non_total_function_typ);
            current_module_name = uu____26529
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26534 = FStar_ST.op_Bang last_env in
    match uu____26534 with
    | [] -> failwith "Empty env stack"
    | uu____26587::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26644  ->
    let uu____26645 = FStar_ST.op_Bang last_env in
    match uu____26645 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___185_26706 = hd1 in
          {
            bindings = (uu___185_26706.bindings);
            depth = (uu___185_26706.depth);
            tcenv = (uu___185_26706.tcenv);
            warn = (uu___185_26706.warn);
            cache = refs;
            nolabels = (uu___185_26706.nolabels);
            use_zfuel_name = (uu___185_26706.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___185_26706.encode_non_total_function_typ);
            current_module_name = (uu___185_26706.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26760  ->
    let uu____26761 = FStar_ST.op_Bang last_env in
    match uu____26761 with
    | [] -> failwith "Popping an empty stack"
    | uu____26814::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26912::uu____26913,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___186_26921 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___186_26921.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___186_26921.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___186_26921.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26922 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26939 =
        let uu____26942 =
          let uu____26943 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26943 in
        let uu____26944 = open_fact_db_tags env in uu____26942 :: uu____26944 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26939
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
      let uu____26968 = encode_sigelt env se in
      match uu____26968 with
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
        let uu____27006 = FStar_Options.log_queries () in
        if uu____27006
        then
          let uu____27009 =
            let uu____27010 =
              let uu____27011 =
                let uu____27012 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____27012 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____27011 in
            FStar_SMTEncoding_Term.Caption uu____27010 in
          uu____27009 :: decls
        else decls in
      (let uu____27023 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27023
       then
         let uu____27024 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27024
       else ());
      (let env =
         let uu____27027 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____27027 tcenv in
       let uu____27028 = encode_top_level_facts env se in
       match uu____27028 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27042 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____27042)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27056 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27056
       then
         let uu____27057 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27057
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27092  ->
                 fun se  ->
                   match uu____27092 with
                   | (g,env2) ->
                       let uu____27112 = encode_top_level_facts env2 se in
                       (match uu____27112 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27135 =
         encode_signature
           (let uu___187_27144 = env in
            {
              bindings = (uu___187_27144.bindings);
              depth = (uu___187_27144.depth);
              tcenv = (uu___187_27144.tcenv);
              warn = false;
              cache = (uu___187_27144.cache);
              nolabels = (uu___187_27144.nolabels);
              use_zfuel_name = (uu___187_27144.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___187_27144.encode_non_total_function_typ);
              current_module_name = (uu___187_27144.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27135 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27161 = FStar_Options.log_queries () in
             if uu____27161
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___188_27169 = env1 in
               {
                 bindings = (uu___188_27169.bindings);
                 depth = (uu___188_27169.depth);
                 tcenv = (uu___188_27169.tcenv);
                 warn = true;
                 cache = (uu___188_27169.cache);
                 nolabels = (uu___188_27169.nolabels);
                 use_zfuel_name = (uu___188_27169.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___188_27169.encode_non_total_function_typ);
                 current_module_name = (uu___188_27169.current_module_name)
               });
            (let uu____27171 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27171
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
        (let uu____27226 =
           let uu____27227 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27227.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27226);
        (let env =
           let uu____27229 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27229 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27241 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27276 = aux rest in
                 (match uu____27276 with
                  | (out,rest1) ->
                      let t =
                        let uu____27306 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27306 with
                        | FStar_Pervasives_Native.Some uu____27311 ->
                            let uu____27312 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27312
                              x.FStar_Syntax_Syntax.sort
                        | uu____27313 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27317 =
                        let uu____27320 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___189_27323 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___189_27323.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___189_27323.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27320 :: out in
                      (uu____27317, rest1))
             | uu____27328 -> ([], bindings1) in
           let uu____27335 = aux bindings in
           match uu____27335 with
           | (closing,bindings1) ->
               let uu____27360 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27360, bindings1) in
         match uu____27241 with
         | (q1,bindings1) ->
             let uu____27383 =
               let uu____27388 =
                 FStar_List.filter
                   (fun uu___154_27393  ->
                      match uu___154_27393 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27394 ->
                          false
                      | uu____27401 -> true) bindings1 in
               encode_env_bindings env uu____27388 in
             (match uu____27383 with
              | (env_decls,env1) ->
                  ((let uu____27419 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27419
                    then
                      let uu____27420 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27420
                    else ());
                   (let uu____27422 = encode_formula q1 env1 in
                    match uu____27422 with
                    | (phi,qdecls) ->
                        let uu____27443 =
                          let uu____27448 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27448 phi in
                        (match uu____27443 with
                         | (labels,phi1) ->
                             let uu____27465 = encode_labels labels in
                             (match uu____27465 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27502 =
                                      let uu____27509 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27510 =
                                        varops.mk_unique "@query" in
                                      (uu____27509,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27510) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27502 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))