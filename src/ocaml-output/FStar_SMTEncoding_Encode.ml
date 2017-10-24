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
      | FStar_Const.Const_range r ->
          (FStar_SMTEncoding_Term.mk_Range_const, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4551 =
            let uu____4552 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4552 in
          failwith uu____4551
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
        (let uu____4581 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4581
         then
           let uu____4582 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4582
         else ());
        (let uu____4584 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4668  ->
                   fun b  ->
                     match uu____4668 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4747 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4763 = gen_term_var env1 x in
                           match uu____4763 with
                           | (xxsym,xx,env') ->
                               let uu____4787 =
                                 let uu____4792 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4792 env1 xx in
                               (match uu____4787 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4747 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4584 with
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
          let uu____4951 = encode_term t env in
          match uu____4951 with
          | (t1,decls) ->
              let uu____4962 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4962, decls)
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
          let uu____4973 = encode_term t env in
          match uu____4973 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4988 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4988, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4990 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4990, decls))
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
        let uu____4996 = encode_args args_e env in
        match uu____4996 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5015 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5024 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5024 in
            let binary arg_tms1 =
              let uu____5037 =
                let uu____5038 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5038 in
              let uu____5039 =
                let uu____5040 =
                  let uu____5041 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5041 in
                FStar_SMTEncoding_Term.unboxInt uu____5040 in
              (uu____5037, uu____5039) in
            let mk_default uu____5047 =
              let uu____5048 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5048 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5099 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5099
              then
                let uu____5100 = let uu____5101 = mk_args ts in op uu____5101 in
                FStar_All.pipe_right uu____5100 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5130 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5130
              then
                let uu____5131 = binary ts in
                match uu____5131 with
                | (t1,t2) ->
                    let uu____5138 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5138
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5142 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5142
                 then
                   let uu____5143 = op (binary ts) in
                   FStar_All.pipe_right uu____5143
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
            let uu____5274 =
              let uu____5283 =
                FStar_List.tryFind
                  (fun uu____5305  ->
                     match uu____5305 with
                     | (l,uu____5315) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5283 FStar_Util.must in
            (match uu____5274 with
             | (uu____5354,op) ->
                 let uu____5364 = op arg_tms in (uu____5364, decls))
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
        let uu____5372 = FStar_List.hd args_e in
        match uu____5372 with
        | (tm_sz,uu____5380) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5390 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5390 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5398 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5398);
                   t_decls) in
            let uu____5399 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5419::(sz_arg,uu____5421)::uu____5422::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5471 =
                    let uu____5474 = FStar_List.tail args_e in
                    FStar_List.tail uu____5474 in
                  let uu____5477 =
                    let uu____5480 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5480 in
                  (uu____5471, uu____5477)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5486::(sz_arg,uu____5488)::uu____5489::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5538 =
                    let uu____5539 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5539 in
                  failwith uu____5538
              | uu____5548 ->
                  let uu____5555 = FStar_List.tail args_e in
                  (uu____5555, FStar_Pervasives_Native.None) in
            (match uu____5399 with
             | (arg_tms,ext_sz) ->
                 let uu____5578 = encode_args arg_tms env in
                 (match uu____5578 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5599 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5608 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5608 in
                      let unary_arith arg_tms2 =
                        let uu____5617 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5617 in
                      let binary arg_tms2 =
                        let uu____5630 =
                          let uu____5631 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5631 in
                        let uu____5632 =
                          let uu____5633 =
                            let uu____5634 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5634 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5633 in
                        (uu____5630, uu____5632) in
                      let binary_arith arg_tms2 =
                        let uu____5649 =
                          let uu____5650 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5650 in
                        let uu____5651 =
                          let uu____5652 =
                            let uu____5653 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5653 in
                          FStar_SMTEncoding_Term.unboxInt uu____5652 in
                        (uu____5649, uu____5651) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5702 =
                          let uu____5703 = mk_args ts in op uu____5703 in
                        FStar_All.pipe_right uu____5702 resBox in
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
                        let uu____5811 =
                          let uu____5814 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5814 in
                        let uu____5816 =
                          let uu____5819 =
                            let uu____5820 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5820 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5819 in
                        mk_bv uu____5811 unary uu____5816 arg_tms2 in
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
                      let uu____6019 =
                        let uu____6028 =
                          FStar_List.tryFind
                            (fun uu____6050  ->
                               match uu____6050 with
                               | (l,uu____6060) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____6028 FStar_Util.must in
                      (match uu____6019 with
                       | (uu____6101,op) ->
                           let uu____6111 = op arg_tms1 in
                           (uu____6111, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6122 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6122
       then
         let uu____6123 = FStar_Syntax_Print.tag_of_term t in
         let uu____6124 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6125 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6123 uu____6124
           uu____6125
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6131 ->
           let uu____6156 =
             let uu____6157 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6158 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6159 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6160 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6157
               uu____6158 uu____6159 uu____6160 in
           failwith uu____6156
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6165 =
             let uu____6166 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6167 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6168 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6169 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6166
               uu____6167 uu____6168 uu____6169 in
           failwith uu____6165
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6175 =
             let uu____6176 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6176 in
           failwith uu____6175
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6183) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6224;
              FStar_Syntax_Syntax.vars = uu____6225;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6242 = varops.fresh "t" in
             (uu____6242, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6245 =
               let uu____6256 =
                 let uu____6259 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6259 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6256) in
             FStar_SMTEncoding_Term.DeclFun uu____6245 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6267) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6277 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6277, [])
       | FStar_Syntax_Syntax.Tm_type uu____6280 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6284) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6309 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6309 with
            | (binders1,res) ->
                let uu____6320 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6320
                then
                  let uu____6325 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6325 with
                   | (vars,guards,env',decls,uu____6350) ->
                       let fsym =
                         let uu____6368 = varops.fresh "f" in
                         (uu____6368, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6371 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___164_6380 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___164_6380.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___164_6380.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___164_6380.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___164_6380.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___164_6380.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___164_6380.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___164_6380.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___164_6380.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___164_6380.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___164_6380.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___164_6380.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___164_6380.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___164_6380.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___164_6380.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___164_6380.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___164_6380.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___164_6380.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___164_6380.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___164_6380.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___164_6380.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___164_6380.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___164_6380.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___164_6380.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___164_6380.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___164_6380.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___164_6380.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___164_6380.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___164_6380.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___164_6380.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___164_6380.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___164_6380.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___164_6380.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6371 with
                        | (pre_opt,res_t) ->
                            let uu____6391 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6391 with
                             | (res_pred,decls') ->
                                 let uu____6402 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6415 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6415, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6419 =
                                         encode_formula pre env' in
                                       (match uu____6419 with
                                        | (guard,decls0) ->
                                            let uu____6432 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6432, decls0)) in
                                 (match uu____6402 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6444 =
                                          let uu____6455 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6455) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6444 in
                                      let cvars =
                                        let uu____6473 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6473
                                          (FStar_List.filter
                                             (fun uu____6487  ->
                                                match uu____6487 with
                                                | (x,uu____6493) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6512 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6512 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6520 =
                                             let uu____6521 =
                                               let uu____6528 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6528) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6521 in
                                           (uu____6520,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6548 =
                                               let uu____6549 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6549 in
                                             varops.mk_unique uu____6548 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6560 =
                                               FStar_Options.log_queries () in
                                             if uu____6560
                                             then
                                               let uu____6563 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6563
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6571 =
                                               let uu____6578 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6578) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6571 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6590 =
                                               let uu____6597 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6597,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6590 in
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
                                             let uu____6618 =
                                               let uu____6625 =
                                                 let uu____6626 =
                                                   let uu____6637 =
                                                     let uu____6638 =
                                                       let uu____6643 =
                                                         let uu____6644 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6644 in
                                                       (f_has_t, uu____6643) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6638 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6637) in
                                                 mkForall_fuel uu____6626 in
                                               (uu____6625,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6618 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6667 =
                                               let uu____6674 =
                                                 let uu____6675 =
                                                   let uu____6686 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6686) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6675 in
                                               (uu____6674,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6667 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6711 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6711);
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
                     let uu____6726 =
                       let uu____6733 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6733,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6726 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6745 =
                       let uu____6752 =
                         let uu____6753 =
                           let uu____6764 =
                             let uu____6765 =
                               let uu____6770 =
                                 let uu____6771 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6771 in
                               (f_has_t, uu____6770) in
                             FStar_SMTEncoding_Util.mkImp uu____6765 in
                           ([[f_has_t]], [fsym], uu____6764) in
                         mkForall_fuel uu____6753 in
                       (uu____6752, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6745 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6798 ->
           let uu____6805 =
             let uu____6810 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6810 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6817;
                 FStar_Syntax_Syntax.vars = uu____6818;_} ->
                 let uu____6825 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6825 with
                  | (b,f1) ->
                      let uu____6850 =
                        let uu____6851 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6851 in
                      (uu____6850, f1))
             | uu____6860 -> failwith "impossible" in
           (match uu____6805 with
            | (x,f) ->
                let uu____6871 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6871 with
                 | (base_t,decls) ->
                     let uu____6882 = gen_term_var env x in
                     (match uu____6882 with
                      | (x1,xtm,env') ->
                          let uu____6896 = encode_formula f env' in
                          (match uu____6896 with
                           | (refinement,decls') ->
                               let uu____6907 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6907 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6923 =
                                        let uu____6926 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6933 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6926
                                          uu____6933 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6923 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6966  ->
                                              match uu____6966 with
                                              | (y,uu____6972) ->
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
                                    let uu____7005 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____7005 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7013 =
                                           let uu____7014 =
                                             let uu____7021 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7021) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7014 in
                                         (uu____7013,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7042 =
                                             let uu____7043 =
                                               let uu____7044 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7044 in
                                             Prims.strcat module_name
                                               uu____7043 in
                                           varops.mk_unique uu____7042 in
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
                                           let uu____7058 =
                                             let uu____7065 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7065) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7058 in
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
                                           let uu____7080 =
                                             let uu____7087 =
                                               let uu____7088 =
                                                 let uu____7099 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7099) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7088 in
                                             (uu____7087,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7080 in
                                         let t_kinding =
                                           let uu____7117 =
                                             let uu____7124 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7124,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7117 in
                                         let t_interp =
                                           let uu____7142 =
                                             let uu____7149 =
                                               let uu____7150 =
                                                 let uu____7161 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7161) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7150 in
                                             let uu____7184 =
                                               let uu____7187 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7187 in
                                             (uu____7149, uu____7184,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7142 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7194 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7194);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7224 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7224 in
           let uu____7225 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7225 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7237 =
                    let uu____7244 =
                      let uu____7245 =
                        let uu____7246 =
                          let uu____7247 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7247 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7246 in
                      varops.mk_unique uu____7245 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7244) in
                  FStar_SMTEncoding_Util.mkAssume uu____7237 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7252 ->
           let uu____7267 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7267 with
            | (head1,args_e) ->
                let uu____7308 =
                  let uu____7321 =
                    let uu____7322 = FStar_Syntax_Subst.compress head1 in
                    uu____7322.FStar_Syntax_Syntax.n in
                  (uu____7321, args_e) in
                (match uu____7308 with
                 | uu____7337 when head_redex env head1 ->
                     let uu____7350 = whnf env t in
                     encode_term uu____7350 env
                 | uu____7351 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7370 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7384;
                       FStar_Syntax_Syntax.vars = uu____7385;_},uu____7386),uu____7387::
                    (v1,uu____7389)::(v2,uu____7391)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7442 = encode_term v1 env in
                     (match uu____7442 with
                      | (v11,decls1) ->
                          let uu____7453 = encode_term v2 env in
                          (match uu____7453 with
                           | (v21,decls2) ->
                               let uu____7464 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7464,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7468::(v1,uu____7470)::(v2,uu____7472)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7519 = encode_term v1 env in
                     (match uu____7519 with
                      | (v11,decls1) ->
                          let uu____7530 = encode_term v2 env in
                          (match uu____7530 with
                           | (v21,decls2) ->
                               let uu____7541 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7541,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7544) ->
                     let e0 =
                       let uu____7562 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7562 in
                     ((let uu____7570 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7570
                       then
                         let uu____7571 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7571
                       else ());
                      (let e =
                         let uu____7576 =
                           let uu____7577 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7578 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7577
                             uu____7578 in
                         uu____7576 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7587),(arg,uu____7589)::[]) -> encode_term arg env
                 | uu____7614 ->
                     let uu____7627 = encode_args args_e env in
                     (match uu____7627 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7682 = encode_term head1 env in
                            match uu____7682 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7746 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7746 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7824  ->
                                                 fun uu____7825  ->
                                                   match (uu____7824,
                                                           uu____7825)
                                                   with
                                                   | ((bv,uu____7847),
                                                      (a,uu____7849)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7867 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7867
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7872 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7872 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7887 =
                                                   let uu____7894 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7903 =
                                                     let uu____7904 =
                                                       let uu____7905 =
                                                         let uu____7906 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7906 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7905 in
                                                     varops.mk_unique
                                                       uu____7904 in
                                                   (uu____7894,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7903) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7887 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7923 = lookup_free_var_sym env fv in
                            match uu____7923 with
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
                                   FStar_Syntax_Syntax.pos = uu____7954;
                                   FStar_Syntax_Syntax.vars = uu____7955;_},uu____7956)
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
                                   FStar_Syntax_Syntax.pos = uu____7967;
                                   FStar_Syntax_Syntax.vars = uu____7968;_},uu____7969)
                                ->
                                let uu____7974 =
                                  let uu____7975 =
                                    let uu____7980 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7980
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7975
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7974
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8010 =
                                  let uu____8011 =
                                    let uu____8016 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8016
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8011
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8010
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8045,(FStar_Util.Inl t1,uu____8047),uu____8048)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8097,(FStar_Util.Inr c,uu____8099),uu____8100)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8149 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8176 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8176 in
                               let uu____8177 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8177 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8193;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8194;_},uu____8195)
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
                                     | uu____8209 ->
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
           let uu____8258 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8258 with
            | (bs1,body1,opening) ->
                let fallback uu____8281 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8288 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8288, [decl]) in
                let is_impure rc =
                  let uu____8295 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8295 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8305 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8305
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8325 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8325
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8329 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8329)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8336 =
                         let uu____8337 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8337 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8336);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8339 =
                       (is_impure rc) &&
                         (let uu____8341 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8341) in
                     if uu____8339
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8348 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8348 with
                        | (vars,guards,envbody,decls,uu____8373) ->
                            let body2 =
                              let uu____8387 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8387
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8389 = encode_term body2 envbody in
                            (match uu____8389 with
                             | (body3,decls') ->
                                 let uu____8400 =
                                   let uu____8409 = codomain_eff rc in
                                   match uu____8409 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8428 = encode_term tfun env in
                                       (match uu____8428 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8400 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8460 =
                                          let uu____8471 =
                                            let uu____8472 =
                                              let uu____8477 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8477, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8472 in
                                          ([], vars, uu____8471) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8460 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8489 =
                                              let uu____8492 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8492
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8489 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8511 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8511 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8519 =
                                             let uu____8520 =
                                               let uu____8527 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8527) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8520 in
                                           (uu____8519,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8538 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8538 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8549 =
                                                    let uu____8550 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8550 = cache_size in
                                                  if uu____8549
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
                                                    let uu____8566 =
                                                      let uu____8567 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8567 in
                                                    varops.mk_unique
                                                      uu____8566 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8574 =
                                                    let uu____8581 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8581) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8574 in
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
                                                      let uu____8599 =
                                                        let uu____8600 =
                                                          let uu____8607 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8607,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8600 in
                                                      [uu____8599] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8620 =
                                                    let uu____8627 =
                                                      let uu____8628 =
                                                        let uu____8639 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8639) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8628 in
                                                    (uu____8627,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8620 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8656 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8656);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8659,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8660;
                          FStar_Syntax_Syntax.lbunivs = uu____8661;
                          FStar_Syntax_Syntax.lbtyp = uu____8662;
                          FStar_Syntax_Syntax.lbeff = uu____8663;
                          FStar_Syntax_Syntax.lbdef = uu____8664;_}::uu____8665),uu____8666)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8692;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8694;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8715 ->
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
              let uu____8785 = encode_term e1 env in
              match uu____8785 with
              | (ee1,decls1) ->
                  let uu____8796 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8796 with
                   | (xs,e21) ->
                       let uu____8821 = FStar_List.hd xs in
                       (match uu____8821 with
                        | (x1,uu____8835) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8837 = encode_body e21 env' in
                            (match uu____8837 with
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
            let uu____8869 =
              let uu____8876 =
                let uu____8877 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8877 in
              gen_term_var env uu____8876 in
            match uu____8869 with
            | (scrsym,scr',env1) ->
                let uu____8885 = encode_term e env1 in
                (match uu____8885 with
                 | (scr,decls) ->
                     let uu____8896 =
                       let encode_branch b uu____8921 =
                         match uu____8921 with
                         | (else_case,decls1) ->
                             let uu____8940 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8940 with
                              | (p,w,br) ->
                                  let uu____8966 = encode_pat env1 p in
                                  (match uu____8966 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9003  ->
                                                   match uu____9003 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9010 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9032 =
                                               encode_term w1 env2 in
                                             (match uu____9032 with
                                              | (w2,decls2) ->
                                                  let uu____9045 =
                                                    let uu____9046 =
                                                      let uu____9051 =
                                                        let uu____9052 =
                                                          let uu____9057 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9057) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9052 in
                                                      (guard, uu____9051) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9046 in
                                                  (uu____9045, decls2)) in
                                       (match uu____9010 with
                                        | (guard1,decls2) ->
                                            let uu____9070 =
                                              encode_br br env2 in
                                            (match uu____9070 with
                                             | (br1,decls3) ->
                                                 let uu____9083 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9083,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8896 with
                      | (match_tm,decls1) ->
                          let uu____9102 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9102, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9142 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9142
       then
         let uu____9143 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9143
       else ());
      (let uu____9145 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9145 with
       | (vars,pat_term) ->
           let uu____9162 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9215  ->
                     fun v1  ->
                       match uu____9215 with
                       | (env1,vars1) ->
                           let uu____9267 = gen_term_var env1 v1 in
                           (match uu____9267 with
                            | (xx,uu____9289,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9162 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9368 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9369 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9370 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9378 = encode_const c env1 in
                      (match uu____9378 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9392::uu____9393 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9396 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9419 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9419 with
                        | (uu____9426,uu____9427::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9430 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9463  ->
                                  match uu____9463 with
                                  | (arg,uu____9471) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9477 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9477)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9504) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9535 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9558 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9602  ->
                                  match uu____9602 with
                                  | (arg,uu____9616) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9622 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9622)) in
                      FStar_All.pipe_right uu____9558 FStar_List.flatten in
                let pat_term1 uu____9650 = encode_term pat_term env1 in
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
      let uu____9660 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9698  ->
                fun uu____9699  ->
                  match (uu____9698, uu____9699) with
                  | ((tms,decls),(t,uu____9735)) ->
                      let uu____9756 = encode_term t env in
                      (match uu____9756 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9660 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9813 = FStar_Syntax_Util.list_elements e in
        match uu____9813 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9834 =
          let uu____9849 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9849 FStar_Syntax_Util.head_and_args in
        match uu____9834 with
        | (head1,args) ->
            let uu____9888 =
              let uu____9901 =
                let uu____9902 = FStar_Syntax_Util.un_uinst head1 in
                uu____9902.FStar_Syntax_Syntax.n in
              (uu____9901, args) in
            (match uu____9888 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9916,uu____9917)::(e,uu____9919)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9954 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9990 =
            let uu____10005 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10005 FStar_Syntax_Util.head_and_args in
          match uu____9990 with
          | (head1,args) ->
              let uu____10046 =
                let uu____10059 =
                  let uu____10060 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10060.FStar_Syntax_Syntax.n in
                (uu____10059, args) in
              (match uu____10046 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10077)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10104 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10126 = smt_pat_or1 t1 in
            (match uu____10126 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10142 = list_elements1 e in
                 FStar_All.pipe_right uu____10142
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10160 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10160
                           (FStar_List.map one_pat)))
             | uu____10171 ->
                 let uu____10176 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10176])
        | uu____10197 ->
            let uu____10200 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10200] in
      let uu____10221 =
        let uu____10240 =
          let uu____10241 = FStar_Syntax_Subst.compress t in
          uu____10241.FStar_Syntax_Syntax.n in
        match uu____10240 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10280 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10280 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10323;
                        FStar_Syntax_Syntax.effect_name = uu____10324;
                        FStar_Syntax_Syntax.result_typ = uu____10325;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10327)::(post,uu____10329)::(pats,uu____10331)::[];
                        FStar_Syntax_Syntax.flags = uu____10332;_}
                      ->
                      let uu____10373 = lemma_pats pats in
                      (binders1, pre, post, uu____10373)
                  | uu____10390 -> failwith "impos"))
        | uu____10409 -> failwith "Impos" in
      match uu____10221 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___165_10457 = env in
            {
              bindings = (uu___165_10457.bindings);
              depth = (uu___165_10457.depth);
              tcenv = (uu___165_10457.tcenv);
              warn = (uu___165_10457.warn);
              cache = (uu___165_10457.cache);
              nolabels = (uu___165_10457.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___165_10457.encode_non_total_function_typ);
              current_module_name = (uu___165_10457.current_module_name)
            } in
          let uu____10458 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10458 with
           | (vars,guards,env2,decls,uu____10483) ->
               let uu____10496 =
                 let uu____10509 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10553 =
                             let uu____10562 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10562
                               FStar_List.unzip in
                           match uu____10553 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10509 FStar_List.unzip in
               (match uu____10496 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___166_10674 = env2 in
                      {
                        bindings = (uu___166_10674.bindings);
                        depth = (uu___166_10674.depth);
                        tcenv = (uu___166_10674.tcenv);
                        warn = (uu___166_10674.warn);
                        cache = (uu___166_10674.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___166_10674.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___166_10674.encode_non_total_function_typ);
                        current_module_name =
                          (uu___166_10674.current_module_name)
                      } in
                    let uu____10675 =
                      let uu____10680 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10680 env3 in
                    (match uu____10675 with
                     | (pre1,decls'') ->
                         let uu____10687 =
                           let uu____10692 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10692 env3 in
                         (match uu____10687 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10702 =
                                let uu____10703 =
                                  let uu____10714 =
                                    let uu____10715 =
                                      let uu____10720 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10720, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10715 in
                                  (pats, vars, uu____10714) in
                                FStar_SMTEncoding_Util.mkForall uu____10703 in
                              (uu____10702, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10739 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10739
        then
          let uu____10740 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10741 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10740 uu____10741
        else () in
      let enc f r l =
        let uu____10774 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10802 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10802 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10774 with
        | (decls,args) ->
            let uu____10831 =
              let uu___167_10832 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___167_10832.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___167_10832.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10831, decls) in
      let const_op f r uu____10863 =
        let uu____10876 = f r in (uu____10876, []) in
      let un_op f l =
        let uu____10895 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10895 in
      let bin_op f uu___141_10911 =
        match uu___141_10911 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10922 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10956 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10979  ->
                 match uu____10979 with
                 | (t,uu____10993) ->
                     let uu____10994 = encode_formula t env in
                     (match uu____10994 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10956 with
        | (decls,phis) ->
            let uu____11023 =
              let uu___168_11024 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___168_11024.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___168_11024.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11023, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11085  ->
               match uu____11085 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11104) -> false
                    | uu____11105 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11120 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11120
        else
          (let uu____11134 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11134 r rf) in
      let mk_imp1 r uu___142_11159 =
        match uu___142_11159 with
        | (lhs,uu____11165)::(rhs,uu____11167)::[] ->
            let uu____11194 = encode_formula rhs env in
            (match uu____11194 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11209) ->
                      (l1, decls1)
                  | uu____11214 ->
                      let uu____11215 = encode_formula lhs env in
                      (match uu____11215 with
                       | (l2,decls2) ->
                           let uu____11226 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11226, (FStar_List.append decls1 decls2)))))
        | uu____11229 -> failwith "impossible" in
      let mk_ite r uu___143_11250 =
        match uu___143_11250 with
        | (guard,uu____11256)::(_then,uu____11258)::(_else,uu____11260)::[]
            ->
            let uu____11297 = encode_formula guard env in
            (match uu____11297 with
             | (g,decls1) ->
                 let uu____11308 = encode_formula _then env in
                 (match uu____11308 with
                  | (t,decls2) ->
                      let uu____11319 = encode_formula _else env in
                      (match uu____11319 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11333 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11358 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11358 in
      let connectives =
        let uu____11376 =
          let uu____11389 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11389) in
        let uu____11406 =
          let uu____11421 =
            let uu____11434 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11434) in
          let uu____11451 =
            let uu____11466 =
              let uu____11481 =
                let uu____11494 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11494) in
              let uu____11511 =
                let uu____11526 =
                  let uu____11541 =
                    let uu____11554 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11554) in
                  [uu____11541;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11526 in
              uu____11481 :: uu____11511 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11466 in
          uu____11421 :: uu____11451 in
        uu____11376 :: uu____11406 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11875 = encode_formula phi' env in
            (match uu____11875 with
             | (phi2,decls) ->
                 let uu____11886 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11886, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11887 ->
            let uu____11894 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11894 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11933 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11933 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11945;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11947;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11968 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11968 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12015::(x,uu____12017)::(t,uu____12019)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12066 = encode_term x env in
                 (match uu____12066 with
                  | (x1,decls) ->
                      let uu____12077 = encode_term t env in
                      (match uu____12077 with
                       | (t1,decls') ->
                           let uu____12088 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12088, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12093)::(msg,uu____12095)::(phi2,uu____12097)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12142 =
                   let uu____12147 =
                     let uu____12148 = FStar_Syntax_Subst.compress r in
                     uu____12148.FStar_Syntax_Syntax.n in
                   let uu____12151 =
                     let uu____12152 = FStar_Syntax_Subst.compress msg in
                     uu____12152.FStar_Syntax_Syntax.n in
                   (uu____12147, uu____12151) in
                 (match uu____12142 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12161))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12167 -> fallback phi2)
             | uu____12172 when head_redex env head2 ->
                 let uu____12185 = whnf env phi1 in
                 encode_formula uu____12185 env
             | uu____12186 ->
                 let uu____12199 = encode_term phi1 env in
                 (match uu____12199 with
                  | (tt,decls) ->
                      let uu____12210 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___169_12213 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___169_12213.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___169_12213.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12210, decls)))
        | uu____12214 ->
            let uu____12215 = encode_term phi1 env in
            (match uu____12215 with
             | (tt,decls) ->
                 let uu____12226 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___170_12229 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___170_12229.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___170_12229.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12226, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12265 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12265 with
        | (vars,guards,env2,decls,uu____12304) ->
            let uu____12317 =
              let uu____12330 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12378 =
                          let uu____12387 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12417  ->
                                    match uu____12417 with
                                    | (t,uu____12427) ->
                                        encode_term t
                                          (let uu___171_12429 = env2 in
                                           {
                                             bindings =
                                               (uu___171_12429.bindings);
                                             depth = (uu___171_12429.depth);
                                             tcenv = (uu___171_12429.tcenv);
                                             warn = (uu___171_12429.warn);
                                             cache = (uu___171_12429.cache);
                                             nolabels =
                                               (uu___171_12429.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___171_12429.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___171_12429.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12387 FStar_List.unzip in
                        match uu____12378 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12330 FStar_List.unzip in
            (match uu____12317 with
             | (pats,decls') ->
                 let uu____12528 = encode_formula body env2 in
                 (match uu____12528 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12560;
                             FStar_SMTEncoding_Term.rng = uu____12561;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12576 -> guards in
                      let uu____12581 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12581, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12641  ->
                   match uu____12641 with
                   | (x,uu____12647) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12655 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12667 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12667) uu____12655 tl1 in
             let uu____12670 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12697  ->
                       match uu____12697 with
                       | (b,uu____12703) ->
                           let uu____12704 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12704)) in
             (match uu____12670 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12710) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12724 =
                    let uu____12725 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12725 in
                  FStar_Errors.warn pos uu____12724) in
       let uu____12726 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12726 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12735 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12793  ->
                     match uu____12793 with
                     | (l,uu____12807) -> FStar_Ident.lid_equals op l)) in
           (match uu____12735 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12840,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12880 = encode_q_body env vars pats body in
             match uu____12880 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12925 =
                     let uu____12936 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12936) in
                   FStar_SMTEncoding_Term.mkForall uu____12925
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12955 = encode_q_body env vars pats body in
             match uu____12955 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12999 =
                   let uu____13000 =
                     let uu____13011 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13011) in
                   FStar_SMTEncoding_Term.mkExists uu____13000
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12999, decls))))
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
  let uu____13109 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13109 with
  | (asym,a) ->
      let uu____13116 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13116 with
       | (xsym,x) ->
           let uu____13123 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13123 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13167 =
                      let uu____13178 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13178, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13167 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13204 =
                      let uu____13211 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13211) in
                    FStar_SMTEncoding_Util.mkApp uu____13204 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13224 =
                    let uu____13227 =
                      let uu____13230 =
                        let uu____13233 =
                          let uu____13234 =
                            let uu____13241 =
                              let uu____13242 =
                                let uu____13253 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13253) in
                              FStar_SMTEncoding_Util.mkForall uu____13242 in
                            (uu____13241, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13234 in
                        let uu____13270 =
                          let uu____13273 =
                            let uu____13274 =
                              let uu____13281 =
                                let uu____13282 =
                                  let uu____13293 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13293) in
                                FStar_SMTEncoding_Util.mkForall uu____13282 in
                              (uu____13281,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13274 in
                          [uu____13273] in
                        uu____13233 :: uu____13270 in
                      xtok_decl :: uu____13230 in
                    xname_decl :: uu____13227 in
                  (xtok1, uu____13224) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13384 =
                    let uu____13397 =
                      let uu____13406 =
                        let uu____13407 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13407 in
                      quant axy uu____13406 in
                    (FStar_Parser_Const.op_Eq, uu____13397) in
                  let uu____13416 =
                    let uu____13431 =
                      let uu____13444 =
                        let uu____13453 =
                          let uu____13454 =
                            let uu____13455 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13455 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13454 in
                        quant axy uu____13453 in
                      (FStar_Parser_Const.op_notEq, uu____13444) in
                    let uu____13464 =
                      let uu____13479 =
                        let uu____13492 =
                          let uu____13501 =
                            let uu____13502 =
                              let uu____13503 =
                                let uu____13508 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13509 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13508, uu____13509) in
                              FStar_SMTEncoding_Util.mkLT uu____13503 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13502 in
                          quant xy uu____13501 in
                        (FStar_Parser_Const.op_LT, uu____13492) in
                      let uu____13518 =
                        let uu____13533 =
                          let uu____13546 =
                            let uu____13555 =
                              let uu____13556 =
                                let uu____13557 =
                                  let uu____13562 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13563 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13562, uu____13563) in
                                FStar_SMTEncoding_Util.mkLTE uu____13557 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13556 in
                            quant xy uu____13555 in
                          (FStar_Parser_Const.op_LTE, uu____13546) in
                        let uu____13572 =
                          let uu____13587 =
                            let uu____13600 =
                              let uu____13609 =
                                let uu____13610 =
                                  let uu____13611 =
                                    let uu____13616 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13617 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13616, uu____13617) in
                                  FStar_SMTEncoding_Util.mkGT uu____13611 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13610 in
                              quant xy uu____13609 in
                            (FStar_Parser_Const.op_GT, uu____13600) in
                          let uu____13626 =
                            let uu____13641 =
                              let uu____13654 =
                                let uu____13663 =
                                  let uu____13664 =
                                    let uu____13665 =
                                      let uu____13670 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13671 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13670, uu____13671) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13665 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13664 in
                                quant xy uu____13663 in
                              (FStar_Parser_Const.op_GTE, uu____13654) in
                            let uu____13680 =
                              let uu____13695 =
                                let uu____13708 =
                                  let uu____13717 =
                                    let uu____13718 =
                                      let uu____13719 =
                                        let uu____13724 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13725 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13724, uu____13725) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13719 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13718 in
                                  quant xy uu____13717 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13708) in
                              let uu____13734 =
                                let uu____13749 =
                                  let uu____13762 =
                                    let uu____13771 =
                                      let uu____13772 =
                                        let uu____13773 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13773 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13772 in
                                    quant qx uu____13771 in
                                  (FStar_Parser_Const.op_Minus, uu____13762) in
                                let uu____13782 =
                                  let uu____13797 =
                                    let uu____13810 =
                                      let uu____13819 =
                                        let uu____13820 =
                                          let uu____13821 =
                                            let uu____13826 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13827 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13826, uu____13827) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13821 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13820 in
                                      quant xy uu____13819 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13810) in
                                  let uu____13836 =
                                    let uu____13851 =
                                      let uu____13864 =
                                        let uu____13873 =
                                          let uu____13874 =
                                            let uu____13875 =
                                              let uu____13880 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13881 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13880, uu____13881) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13875 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13874 in
                                        quant xy uu____13873 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13864) in
                                    let uu____13890 =
                                      let uu____13905 =
                                        let uu____13918 =
                                          let uu____13927 =
                                            let uu____13928 =
                                              let uu____13929 =
                                                let uu____13934 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13935 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13934, uu____13935) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13929 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13928 in
                                          quant xy uu____13927 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13918) in
                                      let uu____13944 =
                                        let uu____13959 =
                                          let uu____13972 =
                                            let uu____13981 =
                                              let uu____13982 =
                                                let uu____13983 =
                                                  let uu____13988 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13989 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13988, uu____13989) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13983 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13982 in
                                            quant xy uu____13981 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13972) in
                                        let uu____13998 =
                                          let uu____14013 =
                                            let uu____14026 =
                                              let uu____14035 =
                                                let uu____14036 =
                                                  let uu____14037 =
                                                    let uu____14042 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14043 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14042,
                                                      uu____14043) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14037 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14036 in
                                              quant xy uu____14035 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14026) in
                                          let uu____14052 =
                                            let uu____14067 =
                                              let uu____14080 =
                                                let uu____14089 =
                                                  let uu____14090 =
                                                    let uu____14091 =
                                                      let uu____14096 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14097 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14096,
                                                        uu____14097) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14091 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14090 in
                                                quant xy uu____14089 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14080) in
                                            let uu____14106 =
                                              let uu____14121 =
                                                let uu____14134 =
                                                  let uu____14143 =
                                                    let uu____14144 =
                                                      let uu____14145 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14145 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14144 in
                                                  quant qx uu____14143 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14134) in
                                              [uu____14121] in
                                            uu____14067 :: uu____14106 in
                                          uu____14013 :: uu____14052 in
                                        uu____13959 :: uu____13998 in
                                      uu____13905 :: uu____13944 in
                                    uu____13851 :: uu____13890 in
                                  uu____13797 :: uu____13836 in
                                uu____13749 :: uu____13782 in
                              uu____13695 :: uu____13734 in
                            uu____13641 :: uu____13680 in
                          uu____13587 :: uu____13626 in
                        uu____13533 :: uu____13572 in
                      uu____13479 :: uu____13518 in
                    uu____13431 :: uu____13464 in
                  uu____13384 :: uu____13416 in
                let mk1 l v1 =
                  let uu____14359 =
                    let uu____14368 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14426  ->
                              match uu____14426 with
                              | (l',uu____14440) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14368
                      (FStar_Option.map
                         (fun uu____14500  ->
                            match uu____14500 with | (uu____14519,b) -> b v1)) in
                  FStar_All.pipe_right uu____14359 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14590  ->
                          match uu____14590 with
                          | (l',uu____14604) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14645 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14645 with
        | (xxsym,xx) ->
            let uu____14652 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14652 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14662 =
                   let uu____14669 =
                     let uu____14670 =
                       let uu____14681 =
                         let uu____14682 =
                           let uu____14687 =
                             let uu____14688 =
                               let uu____14693 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14693) in
                             FStar_SMTEncoding_Util.mkEq uu____14688 in
                           (xx_has_type, uu____14687) in
                         FStar_SMTEncoding_Util.mkImp uu____14682 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14681) in
                     FStar_SMTEncoding_Util.mkForall uu____14670 in
                   let uu____14718 =
                     let uu____14719 =
                       let uu____14720 =
                         let uu____14721 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14721 in
                       Prims.strcat module_name uu____14720 in
                     varops.mk_unique uu____14719 in
                   (uu____14669, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14718) in
                 FStar_SMTEncoding_Util.mkAssume uu____14662)
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
    let uu____14761 =
      let uu____14762 =
        let uu____14769 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14769, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14762 in
    let uu____14772 =
      let uu____14775 =
        let uu____14776 =
          let uu____14783 =
            let uu____14784 =
              let uu____14795 =
                let uu____14796 =
                  let uu____14801 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14801) in
                FStar_SMTEncoding_Util.mkImp uu____14796 in
              ([[typing_pred]], [xx], uu____14795) in
            mkForall_fuel uu____14784 in
          (uu____14783, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14776 in
      [uu____14775] in
    uu____14761 :: uu____14772 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14843 =
      let uu____14844 =
        let uu____14851 =
          let uu____14852 =
            let uu____14863 =
              let uu____14868 =
                let uu____14871 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14871] in
              [uu____14868] in
            let uu____14876 =
              let uu____14877 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14877 tt in
            (uu____14863, [bb], uu____14876) in
          FStar_SMTEncoding_Util.mkForall uu____14852 in
        (uu____14851, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14844 in
    let uu____14898 =
      let uu____14901 =
        let uu____14902 =
          let uu____14909 =
            let uu____14910 =
              let uu____14921 =
                let uu____14922 =
                  let uu____14927 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14927) in
                FStar_SMTEncoding_Util.mkImp uu____14922 in
              ([[typing_pred]], [xx], uu____14921) in
            mkForall_fuel uu____14910 in
          (uu____14909, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14902 in
      [uu____14901] in
    uu____14843 :: uu____14898 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14977 =
        let uu____14978 =
          let uu____14985 =
            let uu____14988 =
              let uu____14991 =
                let uu____14994 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14995 =
                  let uu____14998 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14998] in
                uu____14994 :: uu____14995 in
              tt :: uu____14991 in
            tt :: uu____14988 in
          ("Prims.Precedes", uu____14985) in
        FStar_SMTEncoding_Util.mkApp uu____14978 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14977 in
    let precedes_y_x =
      let uu____15002 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15002 in
    let uu____15005 =
      let uu____15006 =
        let uu____15013 =
          let uu____15014 =
            let uu____15025 =
              let uu____15030 =
                let uu____15033 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15033] in
              [uu____15030] in
            let uu____15038 =
              let uu____15039 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15039 tt in
            (uu____15025, [bb], uu____15038) in
          FStar_SMTEncoding_Util.mkForall uu____15014 in
        (uu____15013, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15006 in
    let uu____15060 =
      let uu____15063 =
        let uu____15064 =
          let uu____15071 =
            let uu____15072 =
              let uu____15083 =
                let uu____15084 =
                  let uu____15089 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15089) in
                FStar_SMTEncoding_Util.mkImp uu____15084 in
              ([[typing_pred]], [xx], uu____15083) in
            mkForall_fuel uu____15072 in
          (uu____15071, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15064 in
      let uu____15114 =
        let uu____15117 =
          let uu____15118 =
            let uu____15125 =
              let uu____15126 =
                let uu____15137 =
                  let uu____15138 =
                    let uu____15143 =
                      let uu____15144 =
                        let uu____15147 =
                          let uu____15150 =
                            let uu____15153 =
                              let uu____15154 =
                                let uu____15159 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15160 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15159, uu____15160) in
                              FStar_SMTEncoding_Util.mkGT uu____15154 in
                            let uu____15161 =
                              let uu____15164 =
                                let uu____15165 =
                                  let uu____15170 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15171 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15170, uu____15171) in
                                FStar_SMTEncoding_Util.mkGTE uu____15165 in
                              let uu____15172 =
                                let uu____15175 =
                                  let uu____15176 =
                                    let uu____15181 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15182 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15181, uu____15182) in
                                  FStar_SMTEncoding_Util.mkLT uu____15176 in
                                [uu____15175] in
                              uu____15164 :: uu____15172 in
                            uu____15153 :: uu____15161 in
                          typing_pred_y :: uu____15150 in
                        typing_pred :: uu____15147 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15144 in
                    (uu____15143, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15138 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15137) in
              mkForall_fuel uu____15126 in
            (uu____15125,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15118 in
        [uu____15117] in
      uu____15063 :: uu____15114 in
    uu____15005 :: uu____15060 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15228 =
      let uu____15229 =
        let uu____15236 =
          let uu____15237 =
            let uu____15248 =
              let uu____15253 =
                let uu____15256 = FStar_SMTEncoding_Term.boxString b in
                [uu____15256] in
              [uu____15253] in
            let uu____15261 =
              let uu____15262 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15262 tt in
            (uu____15248, [bb], uu____15261) in
          FStar_SMTEncoding_Util.mkForall uu____15237 in
        (uu____15236, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15229 in
    let uu____15283 =
      let uu____15286 =
        let uu____15287 =
          let uu____15294 =
            let uu____15295 =
              let uu____15306 =
                let uu____15307 =
                  let uu____15312 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15312) in
                FStar_SMTEncoding_Util.mkImp uu____15307 in
              ([[typing_pred]], [xx], uu____15306) in
            mkForall_fuel uu____15295 in
          (uu____15294, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15287 in
      [uu____15286] in
    uu____15228 :: uu____15283 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15365 =
      let uu____15366 =
        let uu____15373 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15373, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15366 in
    [uu____15365] in
  let mk_and_interp env conj uu____15385 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15410 =
      let uu____15411 =
        let uu____15418 =
          let uu____15419 =
            let uu____15430 =
              let uu____15431 =
                let uu____15436 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15436, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15431 in
            ([[l_and_a_b]], [aa; bb], uu____15430) in
          FStar_SMTEncoding_Util.mkForall uu____15419 in
        (uu____15418, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15411 in
    [uu____15410] in
  let mk_or_interp env disj uu____15474 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15499 =
      let uu____15500 =
        let uu____15507 =
          let uu____15508 =
            let uu____15519 =
              let uu____15520 =
                let uu____15525 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15525, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15520 in
            ([[l_or_a_b]], [aa; bb], uu____15519) in
          FStar_SMTEncoding_Util.mkForall uu____15508 in
        (uu____15507, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15500 in
    [uu____15499] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15588 =
      let uu____15589 =
        let uu____15596 =
          let uu____15597 =
            let uu____15608 =
              let uu____15609 =
                let uu____15614 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15614, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15609 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15608) in
          FStar_SMTEncoding_Util.mkForall uu____15597 in
        (uu____15596, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15589 in
    [uu____15588] in
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
    let uu____15687 =
      let uu____15688 =
        let uu____15695 =
          let uu____15696 =
            let uu____15707 =
              let uu____15708 =
                let uu____15713 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15713, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15708 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15707) in
          FStar_SMTEncoding_Util.mkForall uu____15696 in
        (uu____15695, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15688 in
    [uu____15687] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15784 =
      let uu____15785 =
        let uu____15792 =
          let uu____15793 =
            let uu____15804 =
              let uu____15805 =
                let uu____15810 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15810, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15805 in
            ([[l_imp_a_b]], [aa; bb], uu____15804) in
          FStar_SMTEncoding_Util.mkForall uu____15793 in
        (uu____15792, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15785 in
    [uu____15784] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15873 =
      let uu____15874 =
        let uu____15881 =
          let uu____15882 =
            let uu____15893 =
              let uu____15894 =
                let uu____15899 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15899, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15894 in
            ([[l_iff_a_b]], [aa; bb], uu____15893) in
          FStar_SMTEncoding_Util.mkForall uu____15882 in
        (uu____15881, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15874 in
    [uu____15873] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15951 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15951 in
    let uu____15954 =
      let uu____15955 =
        let uu____15962 =
          let uu____15963 =
            let uu____15974 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15974) in
          FStar_SMTEncoding_Util.mkForall uu____15963 in
        (uu____15962, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15955 in
    [uu____15954] in
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
      let uu____16034 =
        let uu____16041 =
          let uu____16044 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16044] in
        ("Valid", uu____16041) in
      FStar_SMTEncoding_Util.mkApp uu____16034 in
    let uu____16047 =
      let uu____16048 =
        let uu____16055 =
          let uu____16056 =
            let uu____16067 =
              let uu____16068 =
                let uu____16073 =
                  let uu____16074 =
                    let uu____16085 =
                      let uu____16090 =
                        let uu____16093 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16093] in
                      [uu____16090] in
                    let uu____16098 =
                      let uu____16099 =
                        let uu____16104 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16104, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16099 in
                    (uu____16085, [xx1], uu____16098) in
                  FStar_SMTEncoding_Util.mkForall uu____16074 in
                (uu____16073, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16068 in
            ([[l_forall_a_b]], [aa; bb], uu____16067) in
          FStar_SMTEncoding_Util.mkForall uu____16056 in
        (uu____16055, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16048 in
    [uu____16047] in
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
      let uu____16186 =
        let uu____16193 =
          let uu____16196 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16196] in
        ("Valid", uu____16193) in
      FStar_SMTEncoding_Util.mkApp uu____16186 in
    let uu____16199 =
      let uu____16200 =
        let uu____16207 =
          let uu____16208 =
            let uu____16219 =
              let uu____16220 =
                let uu____16225 =
                  let uu____16226 =
                    let uu____16237 =
                      let uu____16242 =
                        let uu____16245 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16245] in
                      [uu____16242] in
                    let uu____16250 =
                      let uu____16251 =
                        let uu____16256 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16256, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16251 in
                    (uu____16237, [xx1], uu____16250) in
                  FStar_SMTEncoding_Util.mkExists uu____16226 in
                (uu____16225, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16220 in
            ([[l_exists_a_b]], [aa; bb], uu____16219) in
          FStar_SMTEncoding_Util.mkForall uu____16208 in
        (uu____16207, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16200 in
    [uu____16199] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16316 =
      let uu____16317 =
        let uu____16324 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16325 = varops.mk_unique "typing_range_const" in
        (uu____16324, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16325) in
      FStar_SMTEncoding_Util.mkAssume uu____16317 in
    [uu____16316] in
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
        let uu____16359 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16359 x1 t in
      let uu____16360 =
        let uu____16371 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16371) in
      FStar_SMTEncoding_Util.mkForall uu____16360 in
    let uu____16394 =
      let uu____16395 =
        let uu____16402 =
          let uu____16403 =
            let uu____16414 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16414) in
          FStar_SMTEncoding_Util.mkForall uu____16403 in
        (uu____16402,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16395 in
    [uu____16394] in
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
          let uu____16738 =
            FStar_Util.find_opt
              (fun uu____16764  ->
                 match uu____16764 with
                 | (l,uu____16776) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16738 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16801,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16840 = encode_function_type_as_formula t env in
        match uu____16840 with
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
              let uu____16886 =
                ((let uu____16889 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16889) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16886
              then
                let uu____16896 = new_term_constant_and_tok_from_lid env lid in
                match uu____16896 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16915 =
                        let uu____16916 = FStar_Syntax_Subst.compress t_norm in
                        uu____16916.FStar_Syntax_Syntax.n in
                      match uu____16915 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16922) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16952  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16957 -> [] in
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
                (let uu____16971 = prims.is lid in
                 if uu____16971
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16979 = prims.mk lid vname in
                   match uu____16979 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17003 =
                      let uu____17014 = curried_arrow_formals_comp t_norm in
                      match uu____17014 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17032 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17032
                            then
                              let uu____17033 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___172_17036 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___172_17036.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___172_17036.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___172_17036.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___172_17036.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___172_17036.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___172_17036.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___172_17036.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___172_17036.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___172_17036.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___172_17036.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___172_17036.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___172_17036.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___172_17036.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___172_17036.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___172_17036.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___172_17036.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___172_17036.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___172_17036.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___172_17036.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___172_17036.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___172_17036.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___172_17036.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___172_17036.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___172_17036.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___172_17036.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___172_17036.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___172_17036.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___172_17036.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___172_17036.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___172_17036.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___172_17036.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___172_17036.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17033
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17048 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17048)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17003 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17093 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17093 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17114 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___144_17156  ->
                                       match uu___144_17156 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17160 =
                                             FStar_Util.prefix vars in
                                           (match uu____17160 with
                                            | (uu____17181,(xxsym,uu____17183))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17201 =
                                                  let uu____17202 =
                                                    let uu____17209 =
                                                      let uu____17210 =
                                                        let uu____17221 =
                                                          let uu____17222 =
                                                            let uu____17227 =
                                                              let uu____17228
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17228 in
                                                            (vapp,
                                                              uu____17227) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17222 in
                                                        ([[vapp]], vars,
                                                          uu____17221) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17210 in
                                                    (uu____17209,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17202 in
                                                [uu____17201])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17247 =
                                             FStar_Util.prefix vars in
                                           (match uu____17247 with
                                            | (uu____17268,(xxsym,uu____17270))
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
                                                let uu____17293 =
                                                  let uu____17294 =
                                                    let uu____17301 =
                                                      let uu____17302 =
                                                        let uu____17313 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17313) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17302 in
                                                    (uu____17301,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17294 in
                                                [uu____17293])
                                       | uu____17330 -> [])) in
                             let uu____17331 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17331 with
                              | (vars,guards,env',decls1,uu____17358) ->
                                  let uu____17371 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17380 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17380, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17382 =
                                          encode_formula p env' in
                                        (match uu____17382 with
                                         | (g,ds) ->
                                             let uu____17393 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17393,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17371 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17406 =
                                           let uu____17413 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17413) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17406 in
                                       let uu____17422 =
                                         let vname_decl =
                                           let uu____17430 =
                                             let uu____17441 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17451  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17441,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17430 in
                                         let uu____17460 =
                                           let env2 =
                                             let uu___173_17466 = env1 in
                                             {
                                               bindings =
                                                 (uu___173_17466.bindings);
                                               depth = (uu___173_17466.depth);
                                               tcenv = (uu___173_17466.tcenv);
                                               warn = (uu___173_17466.warn);
                                               cache = (uu___173_17466.cache);
                                               nolabels =
                                                 (uu___173_17466.nolabels);
                                               use_zfuel_name =
                                                 (uu___173_17466.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___173_17466.current_module_name)
                                             } in
                                           let uu____17467 =
                                             let uu____17468 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17468 in
                                           if uu____17467
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17460 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17483::uu____17484 ->
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
                                                     let uu____17524 =
                                                       let uu____17535 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17535) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17524 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17562 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17565 =
                                               match formals with
                                               | [] ->
                                                   let uu____17582 =
                                                     let uu____17583 =
                                                       let uu____17586 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17586 in
                                                     push_free_var env1 lid
                                                       vname uu____17583 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17582)
                                               | uu____17591 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17598 =
                                                       let uu____17605 =
                                                         let uu____17606 =
                                                           let uu____17617 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17617) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17606 in
                                                       (uu____17605,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17598 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17565 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17422 with
                                        | (decls2,env2) ->
                                            let uu____17660 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17668 =
                                                encode_term res_t1 env' in
                                              match uu____17668 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17681 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17681, decls) in
                                            (match uu____17660 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17692 =
                                                     let uu____17699 =
                                                       let uu____17700 =
                                                         let uu____17711 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17711) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17700 in
                                                     (uu____17699,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17692 in
                                                 let freshness =
                                                   let uu____17727 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17727
                                                   then
                                                     let uu____17732 =
                                                       let uu____17733 =
                                                         let uu____17744 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17755 =
                                                           varops.next_id () in
                                                         (vname, uu____17744,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17755) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17733 in
                                                     let uu____17758 =
                                                       let uu____17761 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17761] in
                                                     uu____17732 ::
                                                       uu____17758
                                                   else [] in
                                                 let g =
                                                   let uu____17766 =
                                                     let uu____17769 =
                                                       let uu____17772 =
                                                         let uu____17775 =
                                                           let uu____17778 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17778 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17775 in
                                                       FStar_List.append
                                                         decls3 uu____17772 in
                                                     FStar_List.append decls2
                                                       uu____17769 in
                                                   FStar_List.append decls11
                                                     uu____17766 in
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
          let uu____17813 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17813 with
          | FStar_Pervasives_Native.None  ->
              let uu____17850 = encode_free_var false env x t t_norm [] in
              (match uu____17850 with
               | (decls,env1) ->
                   let uu____17877 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17877 with
                    | (n1,x',uu____17904) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17925) ->
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
            let uu____17985 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17985 with
            | (decls,env1) ->
                let uu____18004 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18004
                then
                  let uu____18011 =
                    let uu____18014 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18014 in
                  (uu____18011, env1)
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
             (fun uu____18069  ->
                fun lb  ->
                  match uu____18069 with
                  | (decls,env1) ->
                      let uu____18089 =
                        let uu____18096 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18096
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18089 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18118 = FStar_Syntax_Util.head_and_args t in
    match uu____18118 with
    | (hd1,args) ->
        let uu____18155 =
          let uu____18156 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18156.FStar_Syntax_Syntax.n in
        (match uu____18155 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18160,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18179 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18204  ->
      fun quals  ->
        match uu____18204 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18280 = FStar_Util.first_N nbinders formals in
              match uu____18280 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18361  ->
                         fun uu____18362  ->
                           match (uu____18361, uu____18362) with
                           | ((formal,uu____18380),(binder,uu____18382)) ->
                               let uu____18391 =
                                 let uu____18398 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18398) in
                               FStar_Syntax_Syntax.NT uu____18391) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18406 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18437  ->
                              match uu____18437 with
                              | (x,i) ->
                                  let uu____18448 =
                                    let uu___174_18449 = x in
                                    let uu____18450 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___174_18449.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___174_18449.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18450
                                    } in
                                  (uu____18448, i))) in
                    FStar_All.pipe_right uu____18406
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18468 =
                      let uu____18469 = FStar_Syntax_Subst.compress body in
                      let uu____18470 =
                        let uu____18471 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18471 in
                      FStar_Syntax_Syntax.extend_app_n uu____18469
                        uu____18470 in
                    uu____18468 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18532 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18532
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___175_18535 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___175_18535.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___175_18535.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___175_18535.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___175_18535.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___175_18535.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___175_18535.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___175_18535.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___175_18535.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___175_18535.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___175_18535.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___175_18535.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___175_18535.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___175_18535.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___175_18535.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___175_18535.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___175_18535.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___175_18535.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___175_18535.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___175_18535.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___175_18535.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___175_18535.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___175_18535.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___175_18535.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___175_18535.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___175_18535.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___175_18535.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___175_18535.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___175_18535.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___175_18535.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___175_18535.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___175_18535.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___175_18535.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18568 = FStar_Syntax_Util.abs_formals e in
                match uu____18568 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18632::uu____18633 ->
                         let uu____18648 =
                           let uu____18649 =
                             let uu____18652 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18652 in
                           uu____18649.FStar_Syntax_Syntax.n in
                         (match uu____18648 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18695 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18695 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18737 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18737
                                   then
                                     let uu____18772 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18772 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18866  ->
                                                   fun uu____18867  ->
                                                     match (uu____18866,
                                                             uu____18867)
                                                     with
                                                     | ((x,uu____18885),
                                                        (b,uu____18887)) ->
                                                         let uu____18896 =
                                                           let uu____18903 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18903) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18896)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18905 =
                                            let uu____18926 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18926) in
                                          (uu____18905, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18994 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18994 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19083) ->
                              let uu____19088 =
                                let uu____19109 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19109 in
                              (uu____19088, true)
                          | uu____19174 when Prims.op_Negation norm1 ->
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
                          | uu____19176 ->
                              let uu____19177 =
                                let uu____19178 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19179 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19178
                                  uu____19179 in
                              failwith uu____19177)
                     | uu____19204 ->
                         let rec aux' t_norm2 =
                           let uu____19229 =
                             let uu____19230 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19230.FStar_Syntax_Syntax.n in
                           match uu____19229 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19271 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19271 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19299 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19299 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19379)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19384 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19440 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19440
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19452 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19546  ->
                            fun lb  ->
                              match uu____19546 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19641 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19641
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19644 =
                                      let uu____19659 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19659
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19644 with
                                    | (tok,decl,env2) ->
                                        let uu____19705 =
                                          let uu____19718 =
                                            let uu____19729 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19729, tok) in
                                          uu____19718 :: toks in
                                        (uu____19705, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19452 with
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
                        | uu____19912 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19920 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19920 vars)
                            else
                              (let uu____19922 =
                                 let uu____19929 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19929) in
                               FStar_SMTEncoding_Util.mkApp uu____19922) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20011;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20013;
                             FStar_Syntax_Syntax.lbeff = uu____20014;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20077 =
                              let uu____20084 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20084 with
                              | (tcenv',uu____20102,e_t) ->
                                  let uu____20108 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20119 -> failwith "Impossible" in
                                  (match uu____20108 with
                                   | (e1,t_norm1) ->
                                       ((let uu___178_20135 = env2 in
                                         {
                                           bindings =
                                             (uu___178_20135.bindings);
                                           depth = (uu___178_20135.depth);
                                           tcenv = tcenv';
                                           warn = (uu___178_20135.warn);
                                           cache = (uu___178_20135.cache);
                                           nolabels =
                                             (uu___178_20135.nolabels);
                                           use_zfuel_name =
                                             (uu___178_20135.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___178_20135.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___178_20135.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20077 with
                             | (env',e1,t_norm1) ->
                                 let uu____20145 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20145 with
                                  | ((binders,body,uu____20166,uu____20167),curry)
                                      ->
                                      ((let uu____20178 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20178
                                        then
                                          let uu____20179 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20180 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20179 uu____20180
                                        else ());
                                       (let uu____20182 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20182 with
                                        | (vars,guards,env'1,binder_decls,uu____20209)
                                            ->
                                            let body1 =
                                              let uu____20223 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20223
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20226 =
                                              let uu____20235 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20235
                                              then
                                                let uu____20246 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20247 =
                                                  encode_formula body1 env'1 in
                                                (uu____20246, uu____20247)
                                              else
                                                (let uu____20257 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20257)) in
                                            (match uu____20226 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20280 =
                                                     let uu____20287 =
                                                       let uu____20288 =
                                                         let uu____20299 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20299) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20288 in
                                                     let uu____20310 =
                                                       let uu____20313 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20313 in
                                                     (uu____20287,
                                                       uu____20310,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20280 in
                                                 let uu____20316 =
                                                   let uu____20319 =
                                                     let uu____20322 =
                                                       let uu____20325 =
                                                         let uu____20328 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20328 in
                                                       FStar_List.append
                                                         decls2 uu____20325 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20322 in
                                                   FStar_List.append decls1
                                                     uu____20319 in
                                                 (uu____20316, env2))))))
                        | uu____20333 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20418 = varops.fresh "fuel" in
                          (uu____20418, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20421 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20509  ->
                                  fun uu____20510  ->
                                    match (uu____20509, uu____20510) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20658 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20658 in
                                        let gtok =
                                          let uu____20660 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20660 in
                                        let env4 =
                                          let uu____20662 =
                                            let uu____20665 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20665 in
                                          push_free_var env3 flid gtok
                                            uu____20662 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20421 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20821 t_norm
                              uu____20823 =
                              match (uu____20821, uu____20823) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20867;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20868;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20896 =
                                    let uu____20903 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20903 with
                                    | (tcenv',uu____20925,e_t) ->
                                        let uu____20931 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20942 ->
                                              failwith "Impossible" in
                                        (match uu____20931 with
                                         | (e1,t_norm1) ->
                                             ((let uu___179_20958 = env3 in
                                               {
                                                 bindings =
                                                   (uu___179_20958.bindings);
                                                 depth =
                                                   (uu___179_20958.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___179_20958.warn);
                                                 cache =
                                                   (uu___179_20958.cache);
                                                 nolabels =
                                                   (uu___179_20958.nolabels);
                                                 use_zfuel_name =
                                                   (uu___179_20958.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___179_20958.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___179_20958.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20896 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20973 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20973
                                         then
                                           let uu____20974 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20975 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20976 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20974 uu____20975
                                             uu____20976
                                         else ());
                                        (let uu____20978 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20978 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21015 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21015
                                               then
                                                 let uu____21016 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21017 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21018 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21019 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21016 uu____21017
                                                   uu____21018 uu____21019
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21023 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21023 with
                                               | (vars,guards,env'1,binder_decls,uu____21054)
                                                   ->
                                                   let decl_g =
                                                     let uu____21068 =
                                                       let uu____21079 =
                                                         let uu____21082 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21082 in
                                                       (g, uu____21079,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21068 in
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
                                                     let uu____21107 =
                                                       let uu____21114 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21114) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21107 in
                                                   let gsapp =
                                                     let uu____21124 =
                                                       let uu____21131 =
                                                         let uu____21134 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21134 ::
                                                           vars_tm in
                                                       (g, uu____21131) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21124 in
                                                   let gmax =
                                                     let uu____21140 =
                                                       let uu____21147 =
                                                         let uu____21150 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21150 ::
                                                           vars_tm in
                                                       (g, uu____21147) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21140 in
                                                   let body1 =
                                                     let uu____21156 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21156
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21158 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21158 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21176 =
                                                            let uu____21183 =
                                                              let uu____21184
                                                                =
                                                                let uu____21199
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
                                                                  uu____21199) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21184 in
                                                            let uu____21220 =
                                                              let uu____21223
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21223 in
                                                            (uu____21183,
                                                              uu____21220,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21176 in
                                                        let eqn_f =
                                                          let uu____21227 =
                                                            let uu____21234 =
                                                              let uu____21235
                                                                =
                                                                let uu____21246
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21246) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21235 in
                                                            (uu____21234,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21227 in
                                                        let eqn_g' =
                                                          let uu____21260 =
                                                            let uu____21267 =
                                                              let uu____21268
                                                                =
                                                                let uu____21279
                                                                  =
                                                                  let uu____21280
                                                                    =
                                                                    let uu____21285
                                                                    =
                                                                    let uu____21286
                                                                    =
                                                                    let uu____21293
                                                                    =
                                                                    let uu____21296
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21296
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21293) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21286 in
                                                                    (gsapp,
                                                                    uu____21285) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21280 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21279) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21268 in
                                                            (uu____21267,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21260 in
                                                        let uu____21319 =
                                                          let uu____21328 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21328
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21357)
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
                                                                  let uu____21382
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21382
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21387
                                                                  =
                                                                  let uu____21394
                                                                    =
                                                                    let uu____21395
                                                                    =
                                                                    let uu____21406
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21406) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21395 in
                                                                  (uu____21394,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21387 in
                                                              let uu____21427
                                                                =
                                                                let uu____21434
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21434
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21447
                                                                    =
                                                                    let uu____21450
                                                                    =
                                                                    let uu____21451
                                                                    =
                                                                    let uu____21458
                                                                    =
                                                                    let uu____21459
                                                                    =
                                                                    let uu____21470
                                                                    =
                                                                    let uu____21471
                                                                    =
                                                                    let uu____21476
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21476,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21471 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21470) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21459 in
                                                                    (uu____21458,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21451 in
                                                                    [uu____21450] in
                                                                    (d3,
                                                                    uu____21447) in
                                                              (match uu____21427
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21319
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
                            let uu____21541 =
                              let uu____21554 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21633  ->
                                   fun uu____21634  ->
                                     match (uu____21633, uu____21634) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21789 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21789 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21554 in
                            (match uu____21541 with
                             | (decls2,eqns,env01) ->
                                 let uu____21862 =
                                   let isDeclFun uu___145_21874 =
                                     match uu___145_21874 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21875 -> true
                                     | uu____21886 -> false in
                                   let uu____21887 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21887
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21862 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21927 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___146_21931  ->
                                 match uu___146_21931 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21932 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21938 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21938))) in
                      if uu____21927
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
                   let uu____21990 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21990
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
        let uu____22039 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22039 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22043 = encode_sigelt' env se in
      match uu____22043 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22059 =
                  let uu____22060 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22060 in
                [uu____22059]
            | uu____22061 ->
                let uu____22062 =
                  let uu____22065 =
                    let uu____22066 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22066 in
                  uu____22065 :: g in
                let uu____22067 =
                  let uu____22070 =
                    let uu____22071 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22071 in
                  [uu____22070] in
                FStar_List.append uu____22062 uu____22067 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22084 =
          let uu____22085 = FStar_Syntax_Subst.compress t in
          uu____22085.FStar_Syntax_Syntax.n in
        match uu____22084 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22089)) -> s = "opaque_to_smt"
        | uu____22090 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22095 =
          let uu____22096 = FStar_Syntax_Subst.compress t in
          uu____22096.FStar_Syntax_Syntax.n in
        match uu____22095 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22100)) -> s = "uninterpreted_by_smt"
        | uu____22101 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22106 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22111 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22114 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22117 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22132 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22136 =
            let uu____22137 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22137 Prims.op_Negation in
          if uu____22136
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22163 ->
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
               let uu____22183 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22183 with
               | (aname,atok,env2) ->
                   let uu____22199 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22199 with
                    | (formals,uu____22217) ->
                        let uu____22230 =
                          let uu____22235 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22235 env2 in
                        (match uu____22230 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22247 =
                                 let uu____22248 =
                                   let uu____22259 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22275  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22259,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22248 in
                               [uu____22247;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22288 =
                               let aux uu____22340 uu____22341 =
                                 match (uu____22340, uu____22341) with
                                 | ((bv,uu____22393),(env3,acc_sorts,acc)) ->
                                     let uu____22431 = gen_term_var env3 bv in
                                     (match uu____22431 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22288 with
                              | (uu____22503,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22526 =
                                      let uu____22533 =
                                        let uu____22534 =
                                          let uu____22545 =
                                            let uu____22546 =
                                              let uu____22551 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22551) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22546 in
                                          ([[app]], xs_sorts, uu____22545) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22534 in
                                      (uu____22533,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22526 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22571 =
                                      let uu____22578 =
                                        let uu____22579 =
                                          let uu____22590 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22590) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22579 in
                                      (uu____22578,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22571 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22609 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22609 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22637,uu____22638)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22639 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22639 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22656,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22662 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___147_22666  ->
                      match uu___147_22666 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22667 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22672 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22673 -> false)) in
            Prims.op_Negation uu____22662 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22682 =
               let uu____22689 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22689 env fv t quals in
             match uu____22682 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22704 =
                   let uu____22707 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22707 in
                 (uu____22704, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22715 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22715 with
           | (uu____22724,f1) ->
               let uu____22726 = encode_formula f1 env in
               (match uu____22726 with
                | (f2,decls) ->
                    let g =
                      let uu____22740 =
                        let uu____22741 =
                          let uu____22748 =
                            let uu____22751 =
                              let uu____22752 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22752 in
                            FStar_Pervasives_Native.Some uu____22751 in
                          let uu____22753 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22748, uu____22753) in
                        FStar_SMTEncoding_Util.mkAssume uu____22741 in
                      [uu____22740] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22759) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22771 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22789 =
                       let uu____22792 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22792.FStar_Syntax_Syntax.fv_name in
                     uu____22789.FStar_Syntax_Syntax.v in
                   let uu____22793 =
                     let uu____22794 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22794 in
                   if uu____22793
                   then
                     let val_decl =
                       let uu___182_22822 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___182_22822.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___182_22822.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___182_22822.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22827 = encode_sigelt' env1 val_decl in
                     match uu____22827 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22771 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22855,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22857;
                          FStar_Syntax_Syntax.lbtyp = uu____22858;
                          FStar_Syntax_Syntax.lbeff = uu____22859;
                          FStar_Syntax_Syntax.lbdef = uu____22860;_}::[]),uu____22861)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22880 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22880 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22909 =
                   let uu____22912 =
                     let uu____22913 =
                       let uu____22920 =
                         let uu____22921 =
                           let uu____22932 =
                             let uu____22933 =
                               let uu____22938 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22938) in
                             FStar_SMTEncoding_Util.mkEq uu____22933 in
                           ([[b2t_x]], [xx], uu____22932) in
                         FStar_SMTEncoding_Util.mkForall uu____22921 in
                       (uu____22920,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22913 in
                   [uu____22912] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22909 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22971,uu____22972) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___148_22981  ->
                  match uu___148_22981 with
                  | FStar_Syntax_Syntax.Discriminator uu____22982 -> true
                  | uu____22983 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22986,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22997 =
                     let uu____22998 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22998.FStar_Ident.idText in
                   uu____22997 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___149_23002  ->
                     match uu___149_23002 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23003 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23007) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___150_23024  ->
                  match uu___150_23024 with
                  | FStar_Syntax_Syntax.Projector uu____23025 -> true
                  | uu____23030 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23033 = try_lookup_free_var env l in
          (match uu____23033 with
           | FStar_Pervasives_Native.Some uu____23040 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___183_23044 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___183_23044.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___183_23044.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___183_23044.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23051) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23069) ->
          let uu____23078 = encode_sigelts env ses in
          (match uu____23078 with
           | (g,env1) ->
               let uu____23095 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___151_23118  ->
                         match uu___151_23118 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23119;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23120;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23121;_}
                             -> false
                         | uu____23124 -> true)) in
               (match uu____23095 with
                | (g',inversions) ->
                    let uu____23139 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___152_23160  ->
                              match uu___152_23160 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23161 ->
                                  true
                              | uu____23172 -> false)) in
                    (match uu____23139 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23190,tps,k,uu____23193,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___153_23210  ->
                    match uu___153_23210 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23211 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23220 = c in
              match uu____23220 with
              | (name,args,uu____23225,uu____23226,uu____23227) ->
                  let uu____23232 =
                    let uu____23233 =
                      let uu____23244 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23261  ->
                                match uu____23261 with
                                | (uu____23268,sort,uu____23270) -> sort)) in
                      (name, uu____23244, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23233 in
                  [uu____23232]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23297 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23303 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23303 FStar_Option.isNone)) in
            if uu____23297
            then []
            else
              (let uu____23335 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23335 with
               | (xxsym,xx) ->
                   let uu____23344 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23383  ->
                             fun l  ->
                               match uu____23383 with
                               | (out,decls) ->
                                   let uu____23403 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23403 with
                                    | (uu____23414,data_t) ->
                                        let uu____23416 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23416 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23462 =
                                                 let uu____23463 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23463.FStar_Syntax_Syntax.n in
                                               match uu____23462 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23474,indices) ->
                                                   indices
                                               | uu____23496 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23520  ->
                                                         match uu____23520
                                                         with
                                                         | (x,uu____23526) ->
                                                             let uu____23527
                                                               =
                                                               let uu____23528
                                                                 =
                                                                 let uu____23535
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23535,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23528 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23527)
                                                    env) in
                                             let uu____23538 =
                                               encode_args indices env1 in
                                             (match uu____23538 with
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
                                                      let uu____23564 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23580
                                                                 =
                                                                 let uu____23585
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23585,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23580)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23564
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23588 =
                                                      let uu____23589 =
                                                        let uu____23594 =
                                                          let uu____23595 =
                                                            let uu____23600 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23600,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23595 in
                                                        (out, uu____23594) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23589 in
                                                    (uu____23588,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23344 with
                    | (data_ax,decls) ->
                        let uu____23613 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23613 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23624 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23624 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23628 =
                                 let uu____23635 =
                                   let uu____23636 =
                                     let uu____23647 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23662 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23647,
                                       uu____23662) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23636 in
                                 let uu____23677 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23635,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23677) in
                               FStar_SMTEncoding_Util.mkAssume uu____23628 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23680 =
            let uu____23693 =
              let uu____23694 = FStar_Syntax_Subst.compress k in
              uu____23694.FStar_Syntax_Syntax.n in
            match uu____23693 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23739 -> (tps, k) in
          (match uu____23680 with
           | (formals,res) ->
               let uu____23762 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23762 with
                | (formals1,res1) ->
                    let uu____23773 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23773 with
                     | (vars,guards,env',binder_decls,uu____23798) ->
                         let uu____23811 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23811 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23830 =
                                  let uu____23837 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23837) in
                                FStar_SMTEncoding_Util.mkApp uu____23830 in
                              let uu____23846 =
                                let tname_decl =
                                  let uu____23856 =
                                    let uu____23857 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23889  ->
                                              match uu____23889 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23902 = varops.next_id () in
                                    (tname, uu____23857,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23902, false) in
                                  constructor_or_logic_type_decl uu____23856 in
                                let uu____23911 =
                                  match vars with
                                  | [] ->
                                      let uu____23924 =
                                        let uu____23925 =
                                          let uu____23928 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23928 in
                                        push_free_var env1 t tname
                                          uu____23925 in
                                      ([], uu____23924)
                                  | uu____23935 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23944 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23944 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23958 =
                                          let uu____23965 =
                                            let uu____23966 =
                                              let uu____23981 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23981) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23966 in
                                          (uu____23965,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23958 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23911 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23846 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24021 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24021 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24039 =
                                               let uu____24040 =
                                                 let uu____24047 =
                                                   let uu____24048 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24048 in
                                                 (uu____24047,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24040 in
                                             [uu____24039]
                                           else [] in
                                         let uu____24052 =
                                           let uu____24055 =
                                             let uu____24058 =
                                               let uu____24059 =
                                                 let uu____24066 =
                                                   let uu____24067 =
                                                     let uu____24078 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24078) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24067 in
                                                 (uu____24066,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24059 in
                                             [uu____24058] in
                                           FStar_List.append karr uu____24055 in
                                         FStar_List.append decls1 uu____24052 in
                                   let aux =
                                     let uu____24094 =
                                       let uu____24097 =
                                         inversion_axioms tapp vars in
                                       let uu____24100 =
                                         let uu____24103 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24103] in
                                       FStar_List.append uu____24097
                                         uu____24100 in
                                     FStar_List.append kindingAx uu____24094 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24110,uu____24111,uu____24112,uu____24113,uu____24114)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24122,t,uu____24124,n_tps,uu____24126) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24134 = new_term_constant_and_tok_from_lid env d in
          (match uu____24134 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24151 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24151 with
                | (formals,t_res) ->
                    let uu____24186 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24186 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24200 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24200 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24270 =
                                            mk_term_projector_name d x in
                                          (uu____24270,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24272 =
                                  let uu____24291 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24291, true) in
                                FStar_All.pipe_right uu____24272
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
                              let uu____24330 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24330 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24342::uu____24343 ->
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
                                         let uu____24388 =
                                           let uu____24399 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24399) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24388
                                     | uu____24424 -> tok_typing in
                                   let uu____24433 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24433 with
                                    | (vars',guards',env'',decls_formals,uu____24458)
                                        ->
                                        let uu____24471 =
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
                                        (match uu____24471 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24502 ->
                                                   let uu____24509 =
                                                     let uu____24510 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24510 in
                                                   [uu____24509] in
                                             let encode_elim uu____24520 =
                                               let uu____24521 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24521 with
                                               | (head1,args) ->
                                                   let uu____24564 =
                                                     let uu____24565 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24565.FStar_Syntax_Syntax.n in
                                                   (match uu____24564 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24575;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24576;_},uu____24577)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24583 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24583
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
                                                                 | uu____24626
                                                                    ->
                                                                    let uu____24627
                                                                    =
                                                                    let uu____24628
                                                                    =
                                                                    let uu____24633
                                                                    =
                                                                    let uu____24634
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24634 in
                                                                    (uu____24633,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24628 in
                                                                    FStar_Exn.raise
                                                                    uu____24627 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24650
                                                                    =
                                                                    let uu____24651
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24651 in
                                                                    if
                                                                    uu____24650
                                                                    then
                                                                    let uu____24664
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24664]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24666
                                                               =
                                                               let uu____24679
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24729
                                                                     ->
                                                                    fun
                                                                    uu____24730
                                                                     ->
                                                                    match 
                                                                    (uu____24729,
                                                                    uu____24730)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24825
                                                                    =
                                                                    let uu____24832
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24832 in
                                                                    (match uu____24825
                                                                    with
                                                                    | 
                                                                    (uu____24845,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24853
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24853
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24855
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24855
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
                                                                 uu____24679 in
                                                             (match uu____24666
                                                              with
                                                              | (uu____24870,arg_vars,elim_eqns_or_guards,uu____24873)
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
                                                                    let uu____24903
                                                                    =
                                                                    let uu____24910
                                                                    =
                                                                    let uu____24911
                                                                    =
                                                                    let uu____24922
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24933
                                                                    =
                                                                    let uu____24934
                                                                    =
                                                                    let uu____24939
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24939) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24934 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24922,
                                                                    uu____24933) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24911 in
                                                                    (uu____24910,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24903 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24962
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24962,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24964
                                                                    =
                                                                    let uu____24971
                                                                    =
                                                                    let uu____24972
                                                                    =
                                                                    let uu____24983
                                                                    =
                                                                    let uu____24988
                                                                    =
                                                                    let uu____24991
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24991] in
                                                                    [uu____24988] in
                                                                    let uu____24996
                                                                    =
                                                                    let uu____24997
                                                                    =
                                                                    let uu____25002
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25003
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25002,
                                                                    uu____25003) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24997 in
                                                                    (uu____24983,
                                                                    [x],
                                                                    uu____24996) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24972 in
                                                                    let uu____25022
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24971,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25022) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24964
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25029
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
                                                                    (let uu____25057
                                                                    =
                                                                    let uu____25058
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25058
                                                                    dapp1 in
                                                                    [uu____25057]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25029
                                                                    FStar_List.flatten in
                                                                    let uu____25065
                                                                    =
                                                                    let uu____25072
                                                                    =
                                                                    let uu____25073
                                                                    =
                                                                    let uu____25084
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25095
                                                                    =
                                                                    let uu____25096
                                                                    =
                                                                    let uu____25101
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25101) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25096 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25084,
                                                                    uu____25095) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25073 in
                                                                    (uu____25072,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25065) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25122 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25122
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
                                                                 | uu____25165
                                                                    ->
                                                                    let uu____25166
                                                                    =
                                                                    let uu____25167
                                                                    =
                                                                    let uu____25172
                                                                    =
                                                                    let uu____25173
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25173 in
                                                                    (uu____25172,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25167 in
                                                                    FStar_Exn.raise
                                                                    uu____25166 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25189
                                                                    =
                                                                    let uu____25190
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25190 in
                                                                    if
                                                                    uu____25189
                                                                    then
                                                                    let uu____25203
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25203]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25205
                                                               =
                                                               let uu____25218
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25268
                                                                     ->
                                                                    fun
                                                                    uu____25269
                                                                     ->
                                                                    match 
                                                                    (uu____25268,
                                                                    uu____25269)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25364
                                                                    =
                                                                    let uu____25371
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25371 in
                                                                    (match uu____25364
                                                                    with
                                                                    | 
                                                                    (uu____25384,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25392
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25392
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25394
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25394
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
                                                                 uu____25218 in
                                                             (match uu____25205
                                                              with
                                                              | (uu____25409,arg_vars,elim_eqns_or_guards,uu____25412)
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
                                                                    let uu____25442
                                                                    =
                                                                    let uu____25449
                                                                    =
                                                                    let uu____25450
                                                                    =
                                                                    let uu____25461
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25472
                                                                    =
                                                                    let uu____25473
                                                                    =
                                                                    let uu____25478
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25478) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25473 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25461,
                                                                    uu____25472) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25450 in
                                                                    (uu____25449,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25442 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25501
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25501,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25503
                                                                    =
                                                                    let uu____25510
                                                                    =
                                                                    let uu____25511
                                                                    =
                                                                    let uu____25522
                                                                    =
                                                                    let uu____25527
                                                                    =
                                                                    let uu____25530
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25530] in
                                                                    [uu____25527] in
                                                                    let uu____25535
                                                                    =
                                                                    let uu____25536
                                                                    =
                                                                    let uu____25541
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25541,
                                                                    uu____25542) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25536 in
                                                                    (uu____25522,
                                                                    [x],
                                                                    uu____25535) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25511 in
                                                                    let uu____25561
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25510,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25561) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25503
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25568
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
                                                                    (let uu____25596
                                                                    =
                                                                    let uu____25597
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25597
                                                                    dapp1 in
                                                                    [uu____25596]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25568
                                                                    FStar_List.flatten in
                                                                    let uu____25604
                                                                    =
                                                                    let uu____25611
                                                                    =
                                                                    let uu____25612
                                                                    =
                                                                    let uu____25623
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25634
                                                                    =
                                                                    let uu____25635
                                                                    =
                                                                    let uu____25640
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25640) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25635 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25623,
                                                                    uu____25634) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25612 in
                                                                    (uu____25611,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25604) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25659 ->
                                                        ((let uu____25661 =
                                                            let uu____25662 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25663 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25662
                                                              uu____25663 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25661);
                                                         ([], []))) in
                                             let uu____25668 = encode_elim () in
                                             (match uu____25668 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25688 =
                                                      let uu____25691 =
                                                        let uu____25694 =
                                                          let uu____25697 =
                                                            let uu____25700 =
                                                              let uu____25701
                                                                =
                                                                let uu____25712
                                                                  =
                                                                  let uu____25715
                                                                    =
                                                                    let uu____25716
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25716 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25715 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25712) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25701 in
                                                            [uu____25700] in
                                                          let uu____25721 =
                                                            let uu____25724 =
                                                              let uu____25727
                                                                =
                                                                let uu____25730
                                                                  =
                                                                  let uu____25733
                                                                    =
                                                                    let uu____25736
                                                                    =
                                                                    let uu____25739
                                                                    =
                                                                    let uu____25740
                                                                    =
                                                                    let uu____25747
                                                                    =
                                                                    let uu____25748
                                                                    =
                                                                    let uu____25759
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25759) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25748 in
                                                                    (uu____25747,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25740 in
                                                                    let uu____25772
                                                                    =
                                                                    let uu____25775
                                                                    =
                                                                    let uu____25776
                                                                    =
                                                                    let uu____25783
                                                                    =
                                                                    let uu____25784
                                                                    =
                                                                    let uu____25795
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25806
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25795,
                                                                    uu____25806) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25784 in
                                                                    (uu____25783,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25776 in
                                                                    [uu____25775] in
                                                                    uu____25739
                                                                    ::
                                                                    uu____25772 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25736 in
                                                                  FStar_List.append
                                                                    uu____25733
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25730 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25727 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25724 in
                                                          FStar_List.append
                                                            uu____25697
                                                            uu____25721 in
                                                        FStar_List.append
                                                          decls3 uu____25694 in
                                                      FStar_List.append
                                                        decls2 uu____25691 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25688 in
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
           (fun uu____25852  ->
              fun se  ->
                match uu____25852 with
                | (g,env1) ->
                    let uu____25872 = encode_sigelt env1 se in
                    (match uu____25872 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25931 =
        match uu____25931 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25963 ->
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
                 ((let uu____25969 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25969
                   then
                     let uu____25970 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25971 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25972 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25970 uu____25971 uu____25972
                   else ());
                  (let uu____25974 = encode_term t1 env1 in
                   match uu____25974 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25990 =
                         let uu____25997 =
                           let uu____25998 =
                             let uu____25999 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25999
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25998 in
                         new_term_constant_from_string env1 x uu____25997 in
                       (match uu____25990 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26015 = FStar_Options.log_queries () in
                              if uu____26015
                              then
                                let uu____26018 =
                                  let uu____26019 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26020 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26021 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26019 uu____26020 uu____26021 in
                                FStar_Pervasives_Native.Some uu____26018
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26037,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26051 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26051 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26074,se,uu____26076) ->
                 let uu____26081 = encode_sigelt env1 se in
                 (match uu____26081 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26098,se) ->
                 let uu____26104 = encode_sigelt env1 se in
                 (match uu____26104 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26121 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26121 with | (uu____26144,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26159 'Auu____26160 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26160,'Auu____26159)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26228  ->
              match uu____26228 with
              | (l,uu____26240,uu____26241) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26287  ->
              match uu____26287 with
              | (l,uu____26301,uu____26302) ->
                  let uu____26311 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26312 =
                    let uu____26315 =
                      let uu____26316 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26316 in
                    [uu____26315] in
                  uu____26311 :: uu____26312)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26338 =
      let uu____26341 =
        let uu____26342 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26345 =
          let uu____26346 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26346 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26342;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26345
        } in
      [uu____26341] in
    FStar_ST.op_Colon_Equals last_env uu____26338
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26405 = FStar_ST.op_Bang last_env in
      match uu____26405 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26459 ->
          let uu___184_26462 = e in
          let uu____26463 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___184_26462.bindings);
            depth = (uu___184_26462.depth);
            tcenv;
            warn = (uu___184_26462.warn);
            cache = (uu___184_26462.cache);
            nolabels = (uu___184_26462.nolabels);
            use_zfuel_name = (uu___184_26462.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___184_26462.encode_non_total_function_typ);
            current_module_name = uu____26463
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26468 = FStar_ST.op_Bang last_env in
    match uu____26468 with
    | [] -> failwith "Empty env stack"
    | uu____26521::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26578  ->
    let uu____26579 = FStar_ST.op_Bang last_env in
    match uu____26579 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___185_26640 = hd1 in
          {
            bindings = (uu___185_26640.bindings);
            depth = (uu___185_26640.depth);
            tcenv = (uu___185_26640.tcenv);
            warn = (uu___185_26640.warn);
            cache = refs;
            nolabels = (uu___185_26640.nolabels);
            use_zfuel_name = (uu___185_26640.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___185_26640.encode_non_total_function_typ);
            current_module_name = (uu___185_26640.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26694  ->
    let uu____26695 = FStar_ST.op_Bang last_env in
    match uu____26695 with
    | [] -> failwith "Popping an empty stack"
    | uu____26748::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26846::uu____26847,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___186_26855 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___186_26855.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___186_26855.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___186_26855.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26856 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26873 =
        let uu____26876 =
          let uu____26877 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26877 in
        let uu____26878 = open_fact_db_tags env in uu____26876 :: uu____26878 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26873
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
      let uu____26902 = encode_sigelt env se in
      match uu____26902 with
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
        let uu____26940 = FStar_Options.log_queries () in
        if uu____26940
        then
          let uu____26943 =
            let uu____26944 =
              let uu____26945 =
                let uu____26946 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26946 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26945 in
            FStar_SMTEncoding_Term.Caption uu____26944 in
          uu____26943 :: decls
        else decls in
      (let uu____26957 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26957
       then
         let uu____26958 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26958
       else ());
      (let env =
         let uu____26961 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26961 tcenv in
       let uu____26962 = encode_top_level_facts env se in
       match uu____26962 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26976 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26976)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26990 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26990
       then
         let uu____26991 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26991
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27026  ->
                 fun se  ->
                   match uu____27026 with
                   | (g,env2) ->
                       let uu____27046 = encode_top_level_facts env2 se in
                       (match uu____27046 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27069 =
         encode_signature
           (let uu___187_27078 = env in
            {
              bindings = (uu___187_27078.bindings);
              depth = (uu___187_27078.depth);
              tcenv = (uu___187_27078.tcenv);
              warn = false;
              cache = (uu___187_27078.cache);
              nolabels = (uu___187_27078.nolabels);
              use_zfuel_name = (uu___187_27078.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___187_27078.encode_non_total_function_typ);
              current_module_name = (uu___187_27078.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27069 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27095 = FStar_Options.log_queries () in
             if uu____27095
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___188_27103 = env1 in
               {
                 bindings = (uu___188_27103.bindings);
                 depth = (uu___188_27103.depth);
                 tcenv = (uu___188_27103.tcenv);
                 warn = true;
                 cache = (uu___188_27103.cache);
                 nolabels = (uu___188_27103.nolabels);
                 use_zfuel_name = (uu___188_27103.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___188_27103.encode_non_total_function_typ);
                 current_module_name = (uu___188_27103.current_module_name)
               });
            (let uu____27105 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27105
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
        (let uu____27160 =
           let uu____27161 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27161.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27160);
        (let env =
           let uu____27163 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27163 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27175 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27210 = aux rest in
                 (match uu____27210 with
                  | (out,rest1) ->
                      let t =
                        let uu____27240 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27240 with
                        | FStar_Pervasives_Native.Some uu____27245 ->
                            let uu____27246 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27246
                              x.FStar_Syntax_Syntax.sort
                        | uu____27247 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27251 =
                        let uu____27254 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___189_27257 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___189_27257.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___189_27257.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27254 :: out in
                      (uu____27251, rest1))
             | uu____27262 -> ([], bindings1) in
           let uu____27269 = aux bindings in
           match uu____27269 with
           | (closing,bindings1) ->
               let uu____27294 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27294, bindings1) in
         match uu____27175 with
         | (q1,bindings1) ->
             let uu____27317 =
               let uu____27322 =
                 FStar_List.filter
                   (fun uu___154_27327  ->
                      match uu___154_27327 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27328 ->
                          false
                      | uu____27335 -> true) bindings1 in
               encode_env_bindings env uu____27322 in
             (match uu____27317 with
              | (env_decls,env1) ->
                  ((let uu____27353 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27353
                    then
                      let uu____27354 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27354
                    else ());
                   (let uu____27356 = encode_formula q1 env1 in
                    match uu____27356 with
                    | (phi,qdecls) ->
                        let uu____27377 =
                          let uu____27382 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27382 phi in
                        (match uu____27377 with
                         | (labels,phi1) ->
                             let uu____27399 = encode_labels labels in
                             (match uu____27399 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27436 =
                                      let uu____27443 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27444 =
                                        varops.mk_unique "@query" in
                                      (uu____27443,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27444) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27436 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))