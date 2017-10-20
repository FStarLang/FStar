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
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
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
    | uu____4050 ->
        let uu____4051 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____4051)
let is_arithmetic_primitive:
  'Auu____4068 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4068 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4088::uu____4089::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4093::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4096 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4118 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4134 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____4141 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4141)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4180)::uu____4181::uu____4182::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4233)::uu____4234::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4271 -> false
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
          let uu____4478 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4478, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4481 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4481, [])
      | FStar_Const.Const_char c1 ->
          let uu____4485 =
            let uu____4486 =
              let uu____4493 =
                let uu____4496 =
                  let uu____4497 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4497 in
                [uu____4496] in
              ("FStar.Char.Char", uu____4493) in
            FStar_SMTEncoding_Util.mkApp uu____4486 in
          (uu____4485, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4513 =
            let uu____4514 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4514 in
          (uu____4513, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4535) ->
          let uu____4536 = varops.string_const s in (uu____4536, [])
      | FStar_Const.Const_range r ->
          (FStar_SMTEncoding_Term.mk_Range_const, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4545 =
            let uu____4546 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4546 in
          failwith uu____4545
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
        (let uu____4575 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4575
         then
           let uu____4576 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4576
         else ());
        (let uu____4578 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4662  ->
                   fun b  ->
                     match uu____4662 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4741 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4757 = gen_term_var env1 x in
                           match uu____4757 with
                           | (xxsym,xx,env') ->
                               let uu____4781 =
                                 let uu____4786 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4786 env1 xx in
                               (match uu____4781 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4741 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4578 with
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
          let uu____4945 = encode_term t env in
          match uu____4945 with
          | (t1,decls) ->
              let uu____4956 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4956, decls)
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
          let uu____4967 = encode_term t env in
          match uu____4967 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4982 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4982, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4984 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4984, decls))
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
        let uu____4990 = encode_args args_e env in
        match uu____4990 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5009 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5018 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5018 in
            let binary arg_tms1 =
              let uu____5031 =
                let uu____5032 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5032 in
              let uu____5033 =
                let uu____5034 =
                  let uu____5035 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5035 in
                FStar_SMTEncoding_Term.unboxInt uu____5034 in
              (uu____5031, uu____5033) in
            let mk_default uu____5041 =
              let uu____5042 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5042 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5093 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5093
              then
                let uu____5094 = let uu____5095 = mk_args ts in op uu____5095 in
                FStar_All.pipe_right uu____5094 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5124 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5124
              then
                let uu____5125 = binary ts in
                match uu____5125 with
                | (t1,t2) ->
                    let uu____5132 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5132
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5136 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5136
                 then
                   let uu____5137 = op (binary ts) in
                   FStar_All.pipe_right uu____5137
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
            let uu____5268 =
              let uu____5277 =
                FStar_List.tryFind
                  (fun uu____5299  ->
                     match uu____5299 with
                     | (l,uu____5309) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5277 FStar_Util.must in
            (match uu____5268 with
             | (uu____5348,op) ->
                 let uu____5358 = op arg_tms in (uu____5358, decls))
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
        let uu____5366 = FStar_List.hd args_e in
        match uu____5366 with
        | (tm_sz,uu____5374) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5384 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5384 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5392 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5392);
                   t_decls) in
            let uu____5393 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5413::(sz_arg,uu____5415)::uu____5416::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5465 =
                    let uu____5468 = FStar_List.tail args_e in
                    FStar_List.tail uu____5468 in
                  let uu____5471 =
                    let uu____5474 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5474 in
                  (uu____5465, uu____5471)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5480::(sz_arg,uu____5482)::uu____5483::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5532 =
                    let uu____5533 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5533 in
                  failwith uu____5532
              | uu____5542 ->
                  let uu____5549 = FStar_List.tail args_e in
                  (uu____5549, FStar_Pervasives_Native.None) in
            (match uu____5393 with
             | (arg_tms,ext_sz) ->
                 let uu____5572 = encode_args arg_tms env in
                 (match uu____5572 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5593 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5602 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5602 in
                      let unary_arith arg_tms2 =
                        let uu____5611 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5611 in
                      let binary arg_tms2 =
                        let uu____5624 =
                          let uu____5625 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5625 in
                        let uu____5626 =
                          let uu____5627 =
                            let uu____5628 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5628 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5627 in
                        (uu____5624, uu____5626) in
                      let binary_arith arg_tms2 =
                        let uu____5643 =
                          let uu____5644 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5644 in
                        let uu____5645 =
                          let uu____5646 =
                            let uu____5647 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5647 in
                          FStar_SMTEncoding_Term.unboxInt uu____5646 in
                        (uu____5643, uu____5645) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5696 =
                          let uu____5697 = mk_args ts in op uu____5697 in
                        FStar_All.pipe_right uu____5696 resBox in
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
                        let uu____5787 =
                          let uu____5790 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5790 in
                        let uu____5792 =
                          let uu____5795 =
                            let uu____5796 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5796 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5795 in
                        mk_bv uu____5787 unary uu____5792 arg_tms2 in
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
                      let uu____5971 =
                        let uu____5980 =
                          FStar_List.tryFind
                            (fun uu____6002  ->
                               match uu____6002 with
                               | (l,uu____6012) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5980 FStar_Util.must in
                      (match uu____5971 with
                       | (uu____6053,op) ->
                           let uu____6063 = op arg_tms1 in
                           (uu____6063, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6074 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6074
       then
         let uu____6075 = FStar_Syntax_Print.tag_of_term t in
         let uu____6076 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6077 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6075 uu____6076
           uu____6077
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6083 ->
           let uu____6108 =
             let uu____6109 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6110 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6111 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6112 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6109
               uu____6110 uu____6111 uu____6112 in
           failwith uu____6108
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6117 =
             let uu____6118 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6119 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6120 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6121 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6118
               uu____6119 uu____6120 uu____6121 in
           failwith uu____6117
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6127 =
             let uu____6128 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6128 in
           failwith uu____6127
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6135) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6176;
              FStar_Syntax_Syntax.vars = uu____6177;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6194 = varops.fresh "t" in
             (uu____6194, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6197 =
               let uu____6208 =
                 let uu____6211 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6211 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6208) in
             FStar_SMTEncoding_Term.DeclFun uu____6197 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6219) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6229 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6229, [])
       | FStar_Syntax_Syntax.Tm_type uu____6232 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6236) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6261 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6261 with
            | (binders1,res) ->
                let uu____6272 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6272
                then
                  let uu____6277 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6277 with
                   | (vars,guards,env',decls,uu____6302) ->
                       let fsym =
                         let uu____6320 = varops.fresh "f" in
                         (uu____6320, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6323 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___164_6332 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___164_6332.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___164_6332.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___164_6332.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___164_6332.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___164_6332.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___164_6332.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___164_6332.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___164_6332.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___164_6332.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___164_6332.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___164_6332.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___164_6332.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___164_6332.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___164_6332.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___164_6332.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___164_6332.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___164_6332.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___164_6332.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___164_6332.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___164_6332.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___164_6332.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___164_6332.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___164_6332.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___164_6332.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___164_6332.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___164_6332.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___164_6332.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___164_6332.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___164_6332.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___164_6332.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___164_6332.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___164_6332.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6323 with
                        | (pre_opt,res_t) ->
                            let uu____6343 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6343 with
                             | (res_pred,decls') ->
                                 let uu____6354 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6367 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6367, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6371 =
                                         encode_formula pre env' in
                                       (match uu____6371 with
                                        | (guard,decls0) ->
                                            let uu____6384 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6384, decls0)) in
                                 (match uu____6354 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6396 =
                                          let uu____6407 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6407) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6396 in
                                      let cvars =
                                        let uu____6425 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6425
                                          (FStar_List.filter
                                             (fun uu____6439  ->
                                                match uu____6439 with
                                                | (x,uu____6445) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6464 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6464 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6472 =
                                             let uu____6473 =
                                               let uu____6480 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6480) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6473 in
                                           (uu____6472,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6500 =
                                               let uu____6501 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6501 in
                                             varops.mk_unique uu____6500 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6512 =
                                               FStar_Options.log_queries () in
                                             if uu____6512
                                             then
                                               let uu____6515 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6515
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6523 =
                                               let uu____6530 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6530) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6523 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6542 =
                                               let uu____6549 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6549,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6542 in
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
                                             let uu____6570 =
                                               let uu____6577 =
                                                 let uu____6578 =
                                                   let uu____6589 =
                                                     let uu____6590 =
                                                       let uu____6595 =
                                                         let uu____6596 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6596 in
                                                       (f_has_t, uu____6595) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6590 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6589) in
                                                 mkForall_fuel uu____6578 in
                                               (uu____6577,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6570 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6619 =
                                               let uu____6626 =
                                                 let uu____6627 =
                                                   let uu____6638 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6638) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6627 in
                                               (uu____6626,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6619 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6663 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6663);
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
                     let uu____6678 =
                       let uu____6685 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6685,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6678 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6697 =
                       let uu____6704 =
                         let uu____6705 =
                           let uu____6716 =
                             let uu____6717 =
                               let uu____6722 =
                                 let uu____6723 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6723 in
                               (f_has_t, uu____6722) in
                             FStar_SMTEncoding_Util.mkImp uu____6717 in
                           ([[f_has_t]], [fsym], uu____6716) in
                         mkForall_fuel uu____6705 in
                       (uu____6704, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6697 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6750 ->
           let uu____6757 =
             let uu____6762 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6762 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6769;
                 FStar_Syntax_Syntax.vars = uu____6770;_} ->
                 let uu____6777 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6777 with
                  | (b,f1) ->
                      let uu____6802 =
                        let uu____6803 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6803 in
                      (uu____6802, f1))
             | uu____6812 -> failwith "impossible" in
           (match uu____6757 with
            | (x,f) ->
                let uu____6823 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6823 with
                 | (base_t,decls) ->
                     let uu____6834 = gen_term_var env x in
                     (match uu____6834 with
                      | (x1,xtm,env') ->
                          let uu____6848 = encode_formula f env' in
                          (match uu____6848 with
                           | (refinement,decls') ->
                               let uu____6859 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6859 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6875 =
                                        let uu____6878 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6885 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6878
                                          uu____6885 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6875 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6918  ->
                                              match uu____6918 with
                                              | (y,uu____6924) ->
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
                                    let uu____6957 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6957 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6965 =
                                           let uu____6966 =
                                             let uu____6973 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6973) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6966 in
                                         (uu____6965,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6994 =
                                             let uu____6995 =
                                               let uu____6996 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6996 in
                                             Prims.strcat module_name
                                               uu____6995 in
                                           varops.mk_unique uu____6994 in
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
                                           let uu____7010 =
                                             let uu____7017 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7017) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7010 in
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
                                           let uu____7032 =
                                             let uu____7039 =
                                               let uu____7040 =
                                                 let uu____7051 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7051) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7040 in
                                             (uu____7039,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7032 in
                                         let t_kinding =
                                           let uu____7069 =
                                             let uu____7076 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7076,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7069 in
                                         let t_interp =
                                           let uu____7094 =
                                             let uu____7101 =
                                               let uu____7102 =
                                                 let uu____7113 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7113) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7102 in
                                             let uu____7136 =
                                               let uu____7139 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7139 in
                                             (uu____7101, uu____7136,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7094 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7146 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7146);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7176 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7176 in
           let uu____7177 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7177 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7189 =
                    let uu____7196 =
                      let uu____7197 =
                        let uu____7198 =
                          let uu____7199 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7199 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7198 in
                      varops.mk_unique uu____7197 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7196) in
                  FStar_SMTEncoding_Util.mkAssume uu____7189 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7204 ->
           let uu____7219 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7219 with
            | (head1,args_e) ->
                let uu____7260 =
                  let uu____7273 =
                    let uu____7274 = FStar_Syntax_Subst.compress head1 in
                    uu____7274.FStar_Syntax_Syntax.n in
                  (uu____7273, args_e) in
                (match uu____7260 with
                 | uu____7289 when head_redex env head1 ->
                     let uu____7302 = whnf env t in
                     encode_term uu____7302 env
                 | uu____7303 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7322 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7336;
                       FStar_Syntax_Syntax.vars = uu____7337;_},uu____7338),uu____7339::
                    (v1,uu____7341)::(v2,uu____7343)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7394 = encode_term v1 env in
                     (match uu____7394 with
                      | (v11,decls1) ->
                          let uu____7405 = encode_term v2 env in
                          (match uu____7405 with
                           | (v21,decls2) ->
                               let uu____7416 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7416,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7420::(v1,uu____7422)::(v2,uu____7424)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7471 = encode_term v1 env in
                     (match uu____7471 with
                      | (v11,decls1) ->
                          let uu____7482 = encode_term v2 env in
                          (match uu____7482 with
                           | (v21,decls2) ->
                               let uu____7493 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7493,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7496) ->
                     let e0 =
                       let uu____7514 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7514 in
                     ((let uu____7522 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7522
                       then
                         let uu____7523 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7523
                       else ());
                      (let e =
                         let uu____7528 =
                           let uu____7529 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7530 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7529
                             uu____7530 in
                         uu____7528 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7539),(arg,uu____7541)::[]) -> encode_term arg env
                 | uu____7566 ->
                     let uu____7579 = encode_args args_e env in
                     (match uu____7579 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7634 = encode_term head1 env in
                            match uu____7634 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7698 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7698 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7776  ->
                                                 fun uu____7777  ->
                                                   match (uu____7776,
                                                           uu____7777)
                                                   with
                                                   | ((bv,uu____7799),
                                                      (a,uu____7801)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7819 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7819
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7824 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7824 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7839 =
                                                   let uu____7846 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7855 =
                                                     let uu____7856 =
                                                       let uu____7857 =
                                                         let uu____7858 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7858 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7857 in
                                                     varops.mk_unique
                                                       uu____7856 in
                                                   (uu____7846,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7855) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7839 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7875 = lookup_free_var_sym env fv in
                            match uu____7875 with
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
                                   FStar_Syntax_Syntax.pos = uu____7906;
                                   FStar_Syntax_Syntax.vars = uu____7907;_},uu____7908)
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
                                   FStar_Syntax_Syntax.pos = uu____7919;
                                   FStar_Syntax_Syntax.vars = uu____7920;_},uu____7921)
                                ->
                                let uu____7926 =
                                  let uu____7927 =
                                    let uu____7932 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7932
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7927
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7926
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7962 =
                                  let uu____7963 =
                                    let uu____7968 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7968
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7963
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7962
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7997,(FStar_Util.Inl t1,uu____7999),uu____8000)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8049,(FStar_Util.Inr c,uu____8051),uu____8052)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8101 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8128 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8128 in
                               let uu____8129 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8129 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8145;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8146;_},uu____8147)
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
                                     | uu____8161 ->
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
           let uu____8210 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8210 with
            | (bs1,body1,opening) ->
                let fallback uu____8233 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8240 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8240, [decl]) in
                let is_impure rc =
                  let uu____8247 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8247 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8257 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8257
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8277 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8277
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8281 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8281)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8288 =
                         let uu____8289 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8289 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8288);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8291 =
                       (is_impure rc) &&
                         (let uu____8293 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8293) in
                     if uu____8291
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8300 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8300 with
                        | (vars,guards,envbody,decls,uu____8325) ->
                            let body2 =
                              let uu____8339 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8339
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8341 = encode_term body2 envbody in
                            (match uu____8341 with
                             | (body3,decls') ->
                                 let uu____8352 =
                                   let uu____8361 = codomain_eff rc in
                                   match uu____8361 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8380 = encode_term tfun env in
                                       (match uu____8380 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8352 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8412 =
                                          let uu____8423 =
                                            let uu____8424 =
                                              let uu____8429 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8429, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8424 in
                                          ([], vars, uu____8423) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8412 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8441 =
                                              let uu____8444 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8444
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8441 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8463 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8463 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8471 =
                                             let uu____8472 =
                                               let uu____8479 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8479) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8472 in
                                           (uu____8471,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8490 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8490 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8501 =
                                                    let uu____8502 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8502 = cache_size in
                                                  if uu____8501
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
                                                    let uu____8518 =
                                                      let uu____8519 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8519 in
                                                    varops.mk_unique
                                                      uu____8518 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8526 =
                                                    let uu____8533 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8533) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8526 in
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
                                                      let uu____8551 =
                                                        let uu____8552 =
                                                          let uu____8559 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8559,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8552 in
                                                      [uu____8551] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8572 =
                                                    let uu____8579 =
                                                      let uu____8580 =
                                                        let uu____8591 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8591) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8580 in
                                                    (uu____8579,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8572 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8608 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8608);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8611,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8612;
                          FStar_Syntax_Syntax.lbunivs = uu____8613;
                          FStar_Syntax_Syntax.lbtyp = uu____8614;
                          FStar_Syntax_Syntax.lbeff = uu____8615;
                          FStar_Syntax_Syntax.lbdef = uu____8616;_}::uu____8617),uu____8618)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8644;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8646;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8667 ->
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
              let uu____8737 = encode_term e1 env in
              match uu____8737 with
              | (ee1,decls1) ->
                  let uu____8748 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8748 with
                   | (xs,e21) ->
                       let uu____8773 = FStar_List.hd xs in
                       (match uu____8773 with
                        | (x1,uu____8787) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8789 = encode_body e21 env' in
                            (match uu____8789 with
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
            let uu____8821 =
              let uu____8828 =
                let uu____8829 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8829 in
              gen_term_var env uu____8828 in
            match uu____8821 with
            | (scrsym,scr',env1) ->
                let uu____8837 = encode_term e env1 in
                (match uu____8837 with
                 | (scr,decls) ->
                     let uu____8848 =
                       let encode_branch b uu____8873 =
                         match uu____8873 with
                         | (else_case,decls1) ->
                             let uu____8892 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8892 with
                              | (p,w,br) ->
                                  let uu____8918 = encode_pat env1 p in
                                  (match uu____8918 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8955  ->
                                                   match uu____8955 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8962 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8984 =
                                               encode_term w1 env2 in
                                             (match uu____8984 with
                                              | (w2,decls2) ->
                                                  let uu____8997 =
                                                    let uu____8998 =
                                                      let uu____9003 =
                                                        let uu____9004 =
                                                          let uu____9009 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9009) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9004 in
                                                      (guard, uu____9003) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8998 in
                                                  (uu____8997, decls2)) in
                                       (match uu____8962 with
                                        | (guard1,decls2) ->
                                            let uu____9022 =
                                              encode_br br env2 in
                                            (match uu____9022 with
                                             | (br1,decls3) ->
                                                 let uu____9035 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9035,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8848 with
                      | (match_tm,decls1) ->
                          let uu____9054 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9054, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9094 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9094
       then
         let uu____9095 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9095
       else ());
      (let uu____9097 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9097 with
       | (vars,pat_term) ->
           let uu____9114 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9167  ->
                     fun v1  ->
                       match uu____9167 with
                       | (env1,vars1) ->
                           let uu____9219 = gen_term_var env1 v1 in
                           (match uu____9219 with
                            | (xx,uu____9241,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9114 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9320 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9321 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9322 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9330 = encode_const c env1 in
                      (match uu____9330 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9344::uu____9345 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9348 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9371 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9371 with
                        | (uu____9378,uu____9379::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9382 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9415  ->
                                  match uu____9415 with
                                  | (arg,uu____9423) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9429 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9429)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9456) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9487 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9510 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9554  ->
                                  match uu____9554 with
                                  | (arg,uu____9568) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9574 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9574)) in
                      FStar_All.pipe_right uu____9510 FStar_List.flatten in
                let pat_term1 uu____9602 = encode_term pat_term env1 in
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
      let uu____9612 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9650  ->
                fun uu____9651  ->
                  match (uu____9650, uu____9651) with
                  | ((tms,decls),(t,uu____9687)) ->
                      let uu____9708 = encode_term t env in
                      (match uu____9708 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9612 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9765 = FStar_Syntax_Util.list_elements e in
        match uu____9765 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9786 =
          let uu____9801 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9801 FStar_Syntax_Util.head_and_args in
        match uu____9786 with
        | (head1,args) ->
            let uu____9840 =
              let uu____9853 =
                let uu____9854 = FStar_Syntax_Util.un_uinst head1 in
                uu____9854.FStar_Syntax_Syntax.n in
              (uu____9853, args) in
            (match uu____9840 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9868,uu____9869)::(e,uu____9871)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9906 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9942 =
            let uu____9957 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9957 FStar_Syntax_Util.head_and_args in
          match uu____9942 with
          | (head1,args) ->
              let uu____9998 =
                let uu____10011 =
                  let uu____10012 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10012.FStar_Syntax_Syntax.n in
                (uu____10011, args) in
              (match uu____9998 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10029)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10056 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10078 = smt_pat_or1 t1 in
            (match uu____10078 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10094 = list_elements1 e in
                 FStar_All.pipe_right uu____10094
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10112 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10112
                           (FStar_List.map one_pat)))
             | uu____10123 ->
                 let uu____10128 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10128])
        | uu____10149 ->
            let uu____10152 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10152] in
      let uu____10173 =
        let uu____10192 =
          let uu____10193 = FStar_Syntax_Subst.compress t in
          uu____10193.FStar_Syntax_Syntax.n in
        match uu____10192 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10232 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10232 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10275;
                        FStar_Syntax_Syntax.effect_name = uu____10276;
                        FStar_Syntax_Syntax.result_typ = uu____10277;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10279)::(post,uu____10281)::(pats,uu____10283)::[];
                        FStar_Syntax_Syntax.flags = uu____10284;_}
                      ->
                      let uu____10325 = lemma_pats pats in
                      (binders1, pre, post, uu____10325)
                  | uu____10342 -> failwith "impos"))
        | uu____10361 -> failwith "Impos" in
      match uu____10173 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___165_10409 = env in
            {
              bindings = (uu___165_10409.bindings);
              depth = (uu___165_10409.depth);
              tcenv = (uu___165_10409.tcenv);
              warn = (uu___165_10409.warn);
              cache = (uu___165_10409.cache);
              nolabels = (uu___165_10409.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___165_10409.encode_non_total_function_typ);
              current_module_name = (uu___165_10409.current_module_name)
            } in
          let uu____10410 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10410 with
           | (vars,guards,env2,decls,uu____10435) ->
               let uu____10448 =
                 let uu____10461 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10505 =
                             let uu____10514 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10514
                               FStar_List.unzip in
                           match uu____10505 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10461 FStar_List.unzip in
               (match uu____10448 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___166_10626 = env2 in
                      {
                        bindings = (uu___166_10626.bindings);
                        depth = (uu___166_10626.depth);
                        tcenv = (uu___166_10626.tcenv);
                        warn = (uu___166_10626.warn);
                        cache = (uu___166_10626.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___166_10626.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___166_10626.encode_non_total_function_typ);
                        current_module_name =
                          (uu___166_10626.current_module_name)
                      } in
                    let uu____10627 =
                      let uu____10632 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10632 env3 in
                    (match uu____10627 with
                     | (pre1,decls'') ->
                         let uu____10639 =
                           let uu____10644 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10644 env3 in
                         (match uu____10639 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10654 =
                                let uu____10655 =
                                  let uu____10666 =
                                    let uu____10667 =
                                      let uu____10672 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10672, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10667 in
                                  (pats, vars, uu____10666) in
                                FStar_SMTEncoding_Util.mkForall uu____10655 in
                              (uu____10654, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10691 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10691
        then
          let uu____10692 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10693 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10692 uu____10693
        else () in
      let enc f r l =
        let uu____10726 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10754 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10754 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10726 with
        | (decls,args) ->
            let uu____10783 =
              let uu___167_10784 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___167_10784.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___167_10784.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10783, decls) in
      let const_op f r uu____10815 =
        let uu____10828 = f r in (uu____10828, []) in
      let un_op f l =
        let uu____10847 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10847 in
      let bin_op f uu___141_10863 =
        match uu___141_10863 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10874 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10908 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10931  ->
                 match uu____10931 with
                 | (t,uu____10945) ->
                     let uu____10946 = encode_formula t env in
                     (match uu____10946 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10908 with
        | (decls,phis) ->
            let uu____10975 =
              let uu___168_10976 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___168_10976.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___168_10976.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10975, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11037  ->
               match uu____11037 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11056) -> false
                    | uu____11057 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11072 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11072
        else
          (let uu____11086 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11086 r rf) in
      let mk_imp1 r uu___142_11111 =
        match uu___142_11111 with
        | (lhs,uu____11117)::(rhs,uu____11119)::[] ->
            let uu____11146 = encode_formula rhs env in
            (match uu____11146 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11161) ->
                      (l1, decls1)
                  | uu____11166 ->
                      let uu____11167 = encode_formula lhs env in
                      (match uu____11167 with
                       | (l2,decls2) ->
                           let uu____11178 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11178, (FStar_List.append decls1 decls2)))))
        | uu____11181 -> failwith "impossible" in
      let mk_ite r uu___143_11202 =
        match uu___143_11202 with
        | (guard,uu____11208)::(_then,uu____11210)::(_else,uu____11212)::[]
            ->
            let uu____11249 = encode_formula guard env in
            (match uu____11249 with
             | (g,decls1) ->
                 let uu____11260 = encode_formula _then env in
                 (match uu____11260 with
                  | (t,decls2) ->
                      let uu____11271 = encode_formula _else env in
                      (match uu____11271 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11285 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11310 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11310 in
      let connectives =
        let uu____11328 =
          let uu____11341 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11341) in
        let uu____11358 =
          let uu____11373 =
            let uu____11386 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11386) in
          let uu____11403 =
            let uu____11418 =
              let uu____11433 =
                let uu____11446 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11446) in
              let uu____11463 =
                let uu____11478 =
                  let uu____11493 =
                    let uu____11506 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11506) in
                  [uu____11493;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11478 in
              uu____11433 :: uu____11463 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11418 in
          uu____11373 :: uu____11403 in
        uu____11328 :: uu____11358 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11827 = encode_formula phi' env in
            (match uu____11827 with
             | (phi2,decls) ->
                 let uu____11838 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11838, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11839 ->
            let uu____11846 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11846 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11885 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11885 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11897;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11899;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11920 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11920 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11967::(x,uu____11969)::(t,uu____11971)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12018 = encode_term x env in
                 (match uu____12018 with
                  | (x1,decls) ->
                      let uu____12029 = encode_term t env in
                      (match uu____12029 with
                       | (t1,decls') ->
                           let uu____12040 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12040, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12045)::(msg,uu____12047)::(phi2,uu____12049)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12094 =
                   let uu____12099 =
                     let uu____12100 = FStar_Syntax_Subst.compress r in
                     uu____12100.FStar_Syntax_Syntax.n in
                   let uu____12103 =
                     let uu____12104 = FStar_Syntax_Subst.compress msg in
                     uu____12104.FStar_Syntax_Syntax.n in
                   (uu____12099, uu____12103) in
                 (match uu____12094 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12113))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12119 -> fallback phi2)
             | uu____12124 when head_redex env head2 ->
                 let uu____12137 = whnf env phi1 in
                 encode_formula uu____12137 env
             | uu____12138 ->
                 let uu____12151 = encode_term phi1 env in
                 (match uu____12151 with
                  | (tt,decls) ->
                      let uu____12162 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___169_12165 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___169_12165.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___169_12165.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12162, decls)))
        | uu____12166 ->
            let uu____12167 = encode_term phi1 env in
            (match uu____12167 with
             | (tt,decls) ->
                 let uu____12178 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___170_12181 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___170_12181.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___170_12181.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12178, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12217 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12217 with
        | (vars,guards,env2,decls,uu____12256) ->
            let uu____12269 =
              let uu____12282 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12330 =
                          let uu____12339 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12369  ->
                                    match uu____12369 with
                                    | (t,uu____12379) ->
                                        encode_term t
                                          (let uu___171_12381 = env2 in
                                           {
                                             bindings =
                                               (uu___171_12381.bindings);
                                             depth = (uu___171_12381.depth);
                                             tcenv = (uu___171_12381.tcenv);
                                             warn = (uu___171_12381.warn);
                                             cache = (uu___171_12381.cache);
                                             nolabels =
                                               (uu___171_12381.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___171_12381.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___171_12381.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12339 FStar_List.unzip in
                        match uu____12330 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12282 FStar_List.unzip in
            (match uu____12269 with
             | (pats,decls') ->
                 let uu____12480 = encode_formula body env2 in
                 (match uu____12480 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12512;
                             FStar_SMTEncoding_Term.rng = uu____12513;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12528 -> guards in
                      let uu____12533 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12533, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12593  ->
                   match uu____12593 with
                   | (x,uu____12599) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12607 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12619 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12619) uu____12607 tl1 in
             let uu____12622 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12649  ->
                       match uu____12649 with
                       | (b,uu____12655) ->
                           let uu____12656 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12656)) in
             (match uu____12622 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12662) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12676 =
                    let uu____12677 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12677 in
                  FStar_Errors.warn pos uu____12676) in
       let uu____12678 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12678 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12687 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12745  ->
                     match uu____12745 with
                     | (l,uu____12759) -> FStar_Ident.lid_equals op l)) in
           (match uu____12687 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12792,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12832 = encode_q_body env vars pats body in
             match uu____12832 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12877 =
                     let uu____12888 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12888) in
                   FStar_SMTEncoding_Term.mkForall uu____12877
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12907 = encode_q_body env vars pats body in
             match uu____12907 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12951 =
                   let uu____12952 =
                     let uu____12963 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12963) in
                   FStar_SMTEncoding_Term.mkExists uu____12952
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12951, decls))))
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
  let uu____13061 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13061 with
  | (asym,a) ->
      let uu____13068 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13068 with
       | (xsym,x) ->
           let uu____13075 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13075 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13119 =
                      let uu____13130 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13130, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13119 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13156 =
                      let uu____13163 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13163) in
                    FStar_SMTEncoding_Util.mkApp uu____13156 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13176 =
                    let uu____13179 =
                      let uu____13182 =
                        let uu____13185 =
                          let uu____13186 =
                            let uu____13193 =
                              let uu____13194 =
                                let uu____13205 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13205) in
                              FStar_SMTEncoding_Util.mkForall uu____13194 in
                            (uu____13193, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13186 in
                        let uu____13222 =
                          let uu____13225 =
                            let uu____13226 =
                              let uu____13233 =
                                let uu____13234 =
                                  let uu____13245 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13245) in
                                FStar_SMTEncoding_Util.mkForall uu____13234 in
                              (uu____13233,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13226 in
                          [uu____13225] in
                        uu____13185 :: uu____13222 in
                      xtok_decl :: uu____13182 in
                    xname_decl :: uu____13179 in
                  (xtok1, uu____13176) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13336 =
                    let uu____13349 =
                      let uu____13358 =
                        let uu____13359 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13359 in
                      quant axy uu____13358 in
                    (FStar_Parser_Const.op_Eq, uu____13349) in
                  let uu____13368 =
                    let uu____13383 =
                      let uu____13396 =
                        let uu____13405 =
                          let uu____13406 =
                            let uu____13407 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13407 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13406 in
                        quant axy uu____13405 in
                      (FStar_Parser_Const.op_notEq, uu____13396) in
                    let uu____13416 =
                      let uu____13431 =
                        let uu____13444 =
                          let uu____13453 =
                            let uu____13454 =
                              let uu____13455 =
                                let uu____13460 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13461 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13460, uu____13461) in
                              FStar_SMTEncoding_Util.mkLT uu____13455 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13454 in
                          quant xy uu____13453 in
                        (FStar_Parser_Const.op_LT, uu____13444) in
                      let uu____13470 =
                        let uu____13485 =
                          let uu____13498 =
                            let uu____13507 =
                              let uu____13508 =
                                let uu____13509 =
                                  let uu____13514 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13515 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13514, uu____13515) in
                                FStar_SMTEncoding_Util.mkLTE uu____13509 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13508 in
                            quant xy uu____13507 in
                          (FStar_Parser_Const.op_LTE, uu____13498) in
                        let uu____13524 =
                          let uu____13539 =
                            let uu____13552 =
                              let uu____13561 =
                                let uu____13562 =
                                  let uu____13563 =
                                    let uu____13568 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13569 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13568, uu____13569) in
                                  FStar_SMTEncoding_Util.mkGT uu____13563 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13562 in
                              quant xy uu____13561 in
                            (FStar_Parser_Const.op_GT, uu____13552) in
                          let uu____13578 =
                            let uu____13593 =
                              let uu____13606 =
                                let uu____13615 =
                                  let uu____13616 =
                                    let uu____13617 =
                                      let uu____13622 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13623 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13622, uu____13623) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13617 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13616 in
                                quant xy uu____13615 in
                              (FStar_Parser_Const.op_GTE, uu____13606) in
                            let uu____13632 =
                              let uu____13647 =
                                let uu____13660 =
                                  let uu____13669 =
                                    let uu____13670 =
                                      let uu____13671 =
                                        let uu____13676 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13677 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13676, uu____13677) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13671 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13670 in
                                  quant xy uu____13669 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13660) in
                              let uu____13686 =
                                let uu____13701 =
                                  let uu____13714 =
                                    let uu____13723 =
                                      let uu____13724 =
                                        let uu____13725 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13725 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13724 in
                                    quant qx uu____13723 in
                                  (FStar_Parser_Const.op_Minus, uu____13714) in
                                let uu____13734 =
                                  let uu____13749 =
                                    let uu____13762 =
                                      let uu____13771 =
                                        let uu____13772 =
                                          let uu____13773 =
                                            let uu____13778 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13779 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13778, uu____13779) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13773 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13772 in
                                      quant xy uu____13771 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13762) in
                                  let uu____13788 =
                                    let uu____13803 =
                                      let uu____13816 =
                                        let uu____13825 =
                                          let uu____13826 =
                                            let uu____13827 =
                                              let uu____13832 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13833 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13832, uu____13833) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13827 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13826 in
                                        quant xy uu____13825 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13816) in
                                    let uu____13842 =
                                      let uu____13857 =
                                        let uu____13870 =
                                          let uu____13879 =
                                            let uu____13880 =
                                              let uu____13881 =
                                                let uu____13886 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13887 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13886, uu____13887) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13881 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13880 in
                                          quant xy uu____13879 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13870) in
                                      let uu____13896 =
                                        let uu____13911 =
                                          let uu____13924 =
                                            let uu____13933 =
                                              let uu____13934 =
                                                let uu____13935 =
                                                  let uu____13940 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13941 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13940, uu____13941) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13935 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13934 in
                                            quant xy uu____13933 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13924) in
                                        let uu____13950 =
                                          let uu____13965 =
                                            let uu____13978 =
                                              let uu____13987 =
                                                let uu____13988 =
                                                  let uu____13989 =
                                                    let uu____13994 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13995 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13994,
                                                      uu____13995) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13989 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13988 in
                                              quant xy uu____13987 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13978) in
                                          let uu____14004 =
                                            let uu____14019 =
                                              let uu____14032 =
                                                let uu____14041 =
                                                  let uu____14042 =
                                                    let uu____14043 =
                                                      let uu____14048 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14049 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14048,
                                                        uu____14049) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14043 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14042 in
                                                quant xy uu____14041 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14032) in
                                            let uu____14058 =
                                              let uu____14073 =
                                                let uu____14086 =
                                                  let uu____14095 =
                                                    let uu____14096 =
                                                      let uu____14097 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14097 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14096 in
                                                  quant qx uu____14095 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14086) in
                                              [uu____14073] in
                                            uu____14019 :: uu____14058 in
                                          uu____13965 :: uu____14004 in
                                        uu____13911 :: uu____13950 in
                                      uu____13857 :: uu____13896 in
                                    uu____13803 :: uu____13842 in
                                  uu____13749 :: uu____13788 in
                                uu____13701 :: uu____13734 in
                              uu____13647 :: uu____13686 in
                            uu____13593 :: uu____13632 in
                          uu____13539 :: uu____13578 in
                        uu____13485 :: uu____13524 in
                      uu____13431 :: uu____13470 in
                    uu____13383 :: uu____13416 in
                  uu____13336 :: uu____13368 in
                let mk1 l v1 =
                  let uu____14311 =
                    let uu____14320 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14378  ->
                              match uu____14378 with
                              | (l',uu____14392) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14320
                      (FStar_Option.map
                         (fun uu____14452  ->
                            match uu____14452 with | (uu____14471,b) -> b v1)) in
                  FStar_All.pipe_right uu____14311 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14542  ->
                          match uu____14542 with
                          | (l',uu____14556) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14597 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14597 with
        | (xxsym,xx) ->
            let uu____14604 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14604 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14614 =
                   let uu____14621 =
                     let uu____14622 =
                       let uu____14633 =
                         let uu____14634 =
                           let uu____14639 =
                             let uu____14640 =
                               let uu____14645 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14645) in
                             FStar_SMTEncoding_Util.mkEq uu____14640 in
                           (xx_has_type, uu____14639) in
                         FStar_SMTEncoding_Util.mkImp uu____14634 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14633) in
                     FStar_SMTEncoding_Util.mkForall uu____14622 in
                   let uu____14670 =
                     let uu____14671 =
                       let uu____14672 =
                         let uu____14673 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14673 in
                       Prims.strcat module_name uu____14672 in
                     varops.mk_unique uu____14671 in
                   (uu____14621, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14670) in
                 FStar_SMTEncoding_Util.mkAssume uu____14614)
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
    let uu____14713 =
      let uu____14714 =
        let uu____14721 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14721, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14714 in
    let uu____14724 =
      let uu____14727 =
        let uu____14728 =
          let uu____14735 =
            let uu____14736 =
              let uu____14747 =
                let uu____14748 =
                  let uu____14753 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14753) in
                FStar_SMTEncoding_Util.mkImp uu____14748 in
              ([[typing_pred]], [xx], uu____14747) in
            mkForall_fuel uu____14736 in
          (uu____14735, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14728 in
      [uu____14727] in
    uu____14713 :: uu____14724 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14795 =
      let uu____14796 =
        let uu____14803 =
          let uu____14804 =
            let uu____14815 =
              let uu____14820 =
                let uu____14823 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14823] in
              [uu____14820] in
            let uu____14828 =
              let uu____14829 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14829 tt in
            (uu____14815, [bb], uu____14828) in
          FStar_SMTEncoding_Util.mkForall uu____14804 in
        (uu____14803, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14796 in
    let uu____14850 =
      let uu____14853 =
        let uu____14854 =
          let uu____14861 =
            let uu____14862 =
              let uu____14873 =
                let uu____14874 =
                  let uu____14879 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14879) in
                FStar_SMTEncoding_Util.mkImp uu____14874 in
              ([[typing_pred]], [xx], uu____14873) in
            mkForall_fuel uu____14862 in
          (uu____14861, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14854 in
      [uu____14853] in
    uu____14795 :: uu____14850 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14929 =
        let uu____14930 =
          let uu____14937 =
            let uu____14940 =
              let uu____14943 =
                let uu____14946 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14947 =
                  let uu____14950 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14950] in
                uu____14946 :: uu____14947 in
              tt :: uu____14943 in
            tt :: uu____14940 in
          ("Prims.Precedes", uu____14937) in
        FStar_SMTEncoding_Util.mkApp uu____14930 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14929 in
    let precedes_y_x =
      let uu____14954 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14954 in
    let uu____14957 =
      let uu____14958 =
        let uu____14965 =
          let uu____14966 =
            let uu____14977 =
              let uu____14982 =
                let uu____14985 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14985] in
              [uu____14982] in
            let uu____14990 =
              let uu____14991 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14991 tt in
            (uu____14977, [bb], uu____14990) in
          FStar_SMTEncoding_Util.mkForall uu____14966 in
        (uu____14965, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14958 in
    let uu____15012 =
      let uu____15015 =
        let uu____15016 =
          let uu____15023 =
            let uu____15024 =
              let uu____15035 =
                let uu____15036 =
                  let uu____15041 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15041) in
                FStar_SMTEncoding_Util.mkImp uu____15036 in
              ([[typing_pred]], [xx], uu____15035) in
            mkForall_fuel uu____15024 in
          (uu____15023, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15016 in
      let uu____15066 =
        let uu____15069 =
          let uu____15070 =
            let uu____15077 =
              let uu____15078 =
                let uu____15089 =
                  let uu____15090 =
                    let uu____15095 =
                      let uu____15096 =
                        let uu____15099 =
                          let uu____15102 =
                            let uu____15105 =
                              let uu____15106 =
                                let uu____15111 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15112 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15111, uu____15112) in
                              FStar_SMTEncoding_Util.mkGT uu____15106 in
                            let uu____15113 =
                              let uu____15116 =
                                let uu____15117 =
                                  let uu____15122 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15123 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15122, uu____15123) in
                                FStar_SMTEncoding_Util.mkGTE uu____15117 in
                              let uu____15124 =
                                let uu____15127 =
                                  let uu____15128 =
                                    let uu____15133 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15134 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15133, uu____15134) in
                                  FStar_SMTEncoding_Util.mkLT uu____15128 in
                                [uu____15127] in
                              uu____15116 :: uu____15124 in
                            uu____15105 :: uu____15113 in
                          typing_pred_y :: uu____15102 in
                        typing_pred :: uu____15099 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15096 in
                    (uu____15095, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15090 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15089) in
              mkForall_fuel uu____15078 in
            (uu____15077,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15070 in
        [uu____15069] in
      uu____15015 :: uu____15066 in
    uu____14957 :: uu____15012 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15180 =
      let uu____15181 =
        let uu____15188 =
          let uu____15189 =
            let uu____15200 =
              let uu____15205 =
                let uu____15208 = FStar_SMTEncoding_Term.boxString b in
                [uu____15208] in
              [uu____15205] in
            let uu____15213 =
              let uu____15214 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15214 tt in
            (uu____15200, [bb], uu____15213) in
          FStar_SMTEncoding_Util.mkForall uu____15189 in
        (uu____15188, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15181 in
    let uu____15235 =
      let uu____15238 =
        let uu____15239 =
          let uu____15246 =
            let uu____15247 =
              let uu____15258 =
                let uu____15259 =
                  let uu____15264 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15264) in
                FStar_SMTEncoding_Util.mkImp uu____15259 in
              ([[typing_pred]], [xx], uu____15258) in
            mkForall_fuel uu____15247 in
          (uu____15246, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15239 in
      [uu____15238] in
    uu____15180 :: uu____15235 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15317 =
      let uu____15318 =
        let uu____15325 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15325, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15318 in
    [uu____15317] in
  let mk_and_interp env conj uu____15337 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15362 =
      let uu____15363 =
        let uu____15370 =
          let uu____15371 =
            let uu____15382 =
              let uu____15383 =
                let uu____15388 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15388, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15383 in
            ([[l_and_a_b]], [aa; bb], uu____15382) in
          FStar_SMTEncoding_Util.mkForall uu____15371 in
        (uu____15370, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15363 in
    [uu____15362] in
  let mk_or_interp env disj uu____15426 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15451 =
      let uu____15452 =
        let uu____15459 =
          let uu____15460 =
            let uu____15471 =
              let uu____15472 =
                let uu____15477 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15477, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15472 in
            ([[l_or_a_b]], [aa; bb], uu____15471) in
          FStar_SMTEncoding_Util.mkForall uu____15460 in
        (uu____15459, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15452 in
    [uu____15451] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15540 =
      let uu____15541 =
        let uu____15548 =
          let uu____15549 =
            let uu____15560 =
              let uu____15561 =
                let uu____15566 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15566, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15561 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15560) in
          FStar_SMTEncoding_Util.mkForall uu____15549 in
        (uu____15548, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15541 in
    [uu____15540] in
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
    let uu____15639 =
      let uu____15640 =
        let uu____15647 =
          let uu____15648 =
            let uu____15659 =
              let uu____15660 =
                let uu____15665 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15665, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15660 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15659) in
          FStar_SMTEncoding_Util.mkForall uu____15648 in
        (uu____15647, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15640 in
    [uu____15639] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15736 =
      let uu____15737 =
        let uu____15744 =
          let uu____15745 =
            let uu____15756 =
              let uu____15757 =
                let uu____15762 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15762, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15757 in
            ([[l_imp_a_b]], [aa; bb], uu____15756) in
          FStar_SMTEncoding_Util.mkForall uu____15745 in
        (uu____15744, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15737 in
    [uu____15736] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15825 =
      let uu____15826 =
        let uu____15833 =
          let uu____15834 =
            let uu____15845 =
              let uu____15846 =
                let uu____15851 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15851, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15846 in
            ([[l_iff_a_b]], [aa; bb], uu____15845) in
          FStar_SMTEncoding_Util.mkForall uu____15834 in
        (uu____15833, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15826 in
    [uu____15825] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15903 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15903 in
    let uu____15906 =
      let uu____15907 =
        let uu____15914 =
          let uu____15915 =
            let uu____15926 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15926) in
          FStar_SMTEncoding_Util.mkForall uu____15915 in
        (uu____15914, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15907 in
    [uu____15906] in
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
      let uu____15986 =
        let uu____15993 =
          let uu____15996 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15996] in
        ("Valid", uu____15993) in
      FStar_SMTEncoding_Util.mkApp uu____15986 in
    let uu____15999 =
      let uu____16000 =
        let uu____16007 =
          let uu____16008 =
            let uu____16019 =
              let uu____16020 =
                let uu____16025 =
                  let uu____16026 =
                    let uu____16037 =
                      let uu____16042 =
                        let uu____16045 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16045] in
                      [uu____16042] in
                    let uu____16050 =
                      let uu____16051 =
                        let uu____16056 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16056, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16051 in
                    (uu____16037, [xx1], uu____16050) in
                  FStar_SMTEncoding_Util.mkForall uu____16026 in
                (uu____16025, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16020 in
            ([[l_forall_a_b]], [aa; bb], uu____16019) in
          FStar_SMTEncoding_Util.mkForall uu____16008 in
        (uu____16007, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16000 in
    [uu____15999] in
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
      let uu____16138 =
        let uu____16145 =
          let uu____16148 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16148] in
        ("Valid", uu____16145) in
      FStar_SMTEncoding_Util.mkApp uu____16138 in
    let uu____16151 =
      let uu____16152 =
        let uu____16159 =
          let uu____16160 =
            let uu____16171 =
              let uu____16172 =
                let uu____16177 =
                  let uu____16178 =
                    let uu____16189 =
                      let uu____16194 =
                        let uu____16197 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16197] in
                      [uu____16194] in
                    let uu____16202 =
                      let uu____16203 =
                        let uu____16208 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16208, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16203 in
                    (uu____16189, [xx1], uu____16202) in
                  FStar_SMTEncoding_Util.mkExists uu____16178 in
                (uu____16177, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16172 in
            ([[l_exists_a_b]], [aa; bb], uu____16171) in
          FStar_SMTEncoding_Util.mkForall uu____16160 in
        (uu____16159, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16152 in
    [uu____16151] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16268 =
      let uu____16269 =
        let uu____16276 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16277 = varops.mk_unique "typing_range_const" in
        (uu____16276, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16277) in
      FStar_SMTEncoding_Util.mkAssume uu____16269 in
    [uu____16268] in
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
        let uu____16311 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16311 x1 t in
      let uu____16312 =
        let uu____16323 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16323) in
      FStar_SMTEncoding_Util.mkForall uu____16312 in
    let uu____16346 =
      let uu____16347 =
        let uu____16354 =
          let uu____16355 =
            let uu____16366 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16366) in
          FStar_SMTEncoding_Util.mkForall uu____16355 in
        (uu____16354,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16347 in
    [uu____16346] in
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
          let uu____16690 =
            FStar_Util.find_opt
              (fun uu____16716  ->
                 match uu____16716 with
                 | (l,uu____16728) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16690 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16753,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16792 = encode_function_type_as_formula t env in
        match uu____16792 with
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
              let uu____16838 =
                ((let uu____16841 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16841) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16838
              then
                let uu____16848 = new_term_constant_and_tok_from_lid env lid in
                match uu____16848 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16867 =
                        let uu____16868 = FStar_Syntax_Subst.compress t_norm in
                        uu____16868.FStar_Syntax_Syntax.n in
                      match uu____16867 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16874) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16904  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16909 -> [] in
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
                (let uu____16923 = prims.is lid in
                 if uu____16923
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16931 = prims.mk lid vname in
                   match uu____16931 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16955 =
                      let uu____16966 = curried_arrow_formals_comp t_norm in
                      match uu____16966 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16984 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16984
                            then
                              let uu____16985 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___172_16988 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___172_16988.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___172_16988.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___172_16988.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___172_16988.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___172_16988.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___172_16988.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___172_16988.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___172_16988.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___172_16988.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___172_16988.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___172_16988.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___172_16988.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___172_16988.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___172_16988.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___172_16988.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___172_16988.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___172_16988.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___172_16988.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___172_16988.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___172_16988.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___172_16988.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___172_16988.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___172_16988.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___172_16988.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___172_16988.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___172_16988.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___172_16988.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___172_16988.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___172_16988.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___172_16988.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___172_16988.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___172_16988.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16985
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17000 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17000)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16955 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17045 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17045 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17066 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___144_17108  ->
                                       match uu___144_17108 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17112 =
                                             FStar_Util.prefix vars in
                                           (match uu____17112 with
                                            | (uu____17133,(xxsym,uu____17135))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17153 =
                                                  let uu____17154 =
                                                    let uu____17161 =
                                                      let uu____17162 =
                                                        let uu____17173 =
                                                          let uu____17174 =
                                                            let uu____17179 =
                                                              let uu____17180
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17180 in
                                                            (vapp,
                                                              uu____17179) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17174 in
                                                        ([[vapp]], vars,
                                                          uu____17173) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17162 in
                                                    (uu____17161,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17154 in
                                                [uu____17153])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17199 =
                                             FStar_Util.prefix vars in
                                           (match uu____17199 with
                                            | (uu____17220,(xxsym,uu____17222))
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
                                                let uu____17245 =
                                                  let uu____17246 =
                                                    let uu____17253 =
                                                      let uu____17254 =
                                                        let uu____17265 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17265) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17254 in
                                                    (uu____17253,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17246 in
                                                [uu____17245])
                                       | uu____17282 -> [])) in
                             let uu____17283 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17283 with
                              | (vars,guards,env',decls1,uu____17310) ->
                                  let uu____17323 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17332 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17332, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17334 =
                                          encode_formula p env' in
                                        (match uu____17334 with
                                         | (g,ds) ->
                                             let uu____17345 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17345,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17323 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17358 =
                                           let uu____17365 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17365) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17358 in
                                       let uu____17374 =
                                         let vname_decl =
                                           let uu____17382 =
                                             let uu____17393 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17403  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17393,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17382 in
                                         let uu____17412 =
                                           let env2 =
                                             let uu___173_17418 = env1 in
                                             {
                                               bindings =
                                                 (uu___173_17418.bindings);
                                               depth = (uu___173_17418.depth);
                                               tcenv = (uu___173_17418.tcenv);
                                               warn = (uu___173_17418.warn);
                                               cache = (uu___173_17418.cache);
                                               nolabels =
                                                 (uu___173_17418.nolabels);
                                               use_zfuel_name =
                                                 (uu___173_17418.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___173_17418.current_module_name)
                                             } in
                                           let uu____17419 =
                                             let uu____17420 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17420 in
                                           if uu____17419
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17412 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17435::uu____17436 ->
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
                                                     let uu____17476 =
                                                       let uu____17487 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17487) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17476 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17514 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17517 =
                                               match formals with
                                               | [] ->
                                                   let uu____17534 =
                                                     let uu____17535 =
                                                       let uu____17538 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17538 in
                                                     push_free_var env1 lid
                                                       vname uu____17535 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17534)
                                               | uu____17543 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17550 =
                                                       let uu____17557 =
                                                         let uu____17558 =
                                                           let uu____17569 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17569) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17558 in
                                                       (uu____17557,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17550 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17517 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17374 with
                                        | (decls2,env2) ->
                                            let uu____17612 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17620 =
                                                encode_term res_t1 env' in
                                              match uu____17620 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17633 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17633, decls) in
                                            (match uu____17612 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17644 =
                                                     let uu____17651 =
                                                       let uu____17652 =
                                                         let uu____17663 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17663) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17652 in
                                                     (uu____17651,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17644 in
                                                 let freshness =
                                                   let uu____17679 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17679
                                                   then
                                                     let uu____17684 =
                                                       let uu____17685 =
                                                         let uu____17696 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17707 =
                                                           varops.next_id () in
                                                         (vname, uu____17696,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17707) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17685 in
                                                     let uu____17710 =
                                                       let uu____17713 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17713] in
                                                     uu____17684 ::
                                                       uu____17710
                                                   else [] in
                                                 let g =
                                                   let uu____17718 =
                                                     let uu____17721 =
                                                       let uu____17724 =
                                                         let uu____17727 =
                                                           let uu____17730 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17730 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17727 in
                                                       FStar_List.append
                                                         decls3 uu____17724 in
                                                     FStar_List.append decls2
                                                       uu____17721 in
                                                   FStar_List.append decls11
                                                     uu____17718 in
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
          let uu____17765 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17765 with
          | FStar_Pervasives_Native.None  ->
              let uu____17802 = encode_free_var false env x t t_norm [] in
              (match uu____17802 with
               | (decls,env1) ->
                   let uu____17829 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17829 with
                    | (n1,x',uu____17856) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17877) ->
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
            let uu____17937 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17937 with
            | (decls,env1) ->
                let uu____17956 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17956
                then
                  let uu____17963 =
                    let uu____17966 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17966 in
                  (uu____17963, env1)
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
             (fun uu____18021  ->
                fun lb  ->
                  match uu____18021 with
                  | (decls,env1) ->
                      let uu____18041 =
                        let uu____18048 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18048
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18041 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18070 = FStar_Syntax_Util.head_and_args t in
    match uu____18070 with
    | (hd1,args) ->
        let uu____18107 =
          let uu____18108 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18108.FStar_Syntax_Syntax.n in
        (match uu____18107 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18112,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18131 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18156  ->
      fun quals  ->
        match uu____18156 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18232 = FStar_Util.first_N nbinders formals in
              match uu____18232 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18313  ->
                         fun uu____18314  ->
                           match (uu____18313, uu____18314) with
                           | ((formal,uu____18332),(binder,uu____18334)) ->
                               let uu____18343 =
                                 let uu____18350 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18350) in
                               FStar_Syntax_Syntax.NT uu____18343) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18358 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18389  ->
                              match uu____18389 with
                              | (x,i) ->
                                  let uu____18400 =
                                    let uu___174_18401 = x in
                                    let uu____18402 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___174_18401.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___174_18401.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18402
                                    } in
                                  (uu____18400, i))) in
                    FStar_All.pipe_right uu____18358
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18420 =
                      let uu____18421 = FStar_Syntax_Subst.compress body in
                      let uu____18422 =
                        let uu____18423 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18423 in
                      FStar_Syntax_Syntax.extend_app_n uu____18421
                        uu____18422 in
                    uu____18420 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18484 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18484
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___175_18487 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___175_18487.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___175_18487.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___175_18487.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___175_18487.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___175_18487.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___175_18487.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___175_18487.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___175_18487.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___175_18487.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___175_18487.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___175_18487.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___175_18487.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___175_18487.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___175_18487.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___175_18487.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___175_18487.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___175_18487.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___175_18487.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___175_18487.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___175_18487.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___175_18487.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___175_18487.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___175_18487.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___175_18487.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___175_18487.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___175_18487.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___175_18487.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___175_18487.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___175_18487.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___175_18487.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___175_18487.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___175_18487.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18520 = FStar_Syntax_Util.abs_formals e in
                match uu____18520 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18584::uu____18585 ->
                         let uu____18600 =
                           let uu____18601 =
                             let uu____18604 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18604 in
                           uu____18601.FStar_Syntax_Syntax.n in
                         (match uu____18600 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18647 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18647 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18689 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18689
                                   then
                                     let uu____18724 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18724 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18818  ->
                                                   fun uu____18819  ->
                                                     match (uu____18818,
                                                             uu____18819)
                                                     with
                                                     | ((x,uu____18837),
                                                        (b,uu____18839)) ->
                                                         let uu____18848 =
                                                           let uu____18855 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18855) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18848)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18857 =
                                            let uu____18878 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18878) in
                                          (uu____18857, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18946 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18946 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19035) ->
                              let uu____19040 =
                                let uu____19061 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19061 in
                              (uu____19040, true)
                          | uu____19126 when Prims.op_Negation norm1 ->
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
                          | uu____19128 ->
                              let uu____19129 =
                                let uu____19130 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19131 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19130
                                  uu____19131 in
                              failwith uu____19129)
                     | uu____19156 ->
                         let uu____19157 =
                           let uu____19158 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19158.FStar_Syntax_Syntax.n in
                         (match uu____19157 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19203 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19203 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19235 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19235 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19318 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19374 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19374
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19386 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19480  ->
                            fun lb  ->
                              match uu____19480 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19575 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19575
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19578 =
                                      let uu____19593 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19593
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19578 with
                                    | (tok,decl,env2) ->
                                        let uu____19639 =
                                          let uu____19652 =
                                            let uu____19663 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19663, tok) in
                                          uu____19652 :: toks in
                                        (uu____19639, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19386 with
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
                        | uu____19846 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19854 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19854 vars)
                            else
                              (let uu____19856 =
                                 let uu____19863 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19863) in
                               FStar_SMTEncoding_Util.mkApp uu____19856) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19945;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19947;
                             FStar_Syntax_Syntax.lbeff = uu____19948;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20011 =
                              let uu____20018 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20018 with
                              | (tcenv',uu____20036,e_t) ->
                                  let uu____20042 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20053 -> failwith "Impossible" in
                                  (match uu____20042 with
                                   | (e1,t_norm1) ->
                                       ((let uu___178_20069 = env2 in
                                         {
                                           bindings =
                                             (uu___178_20069.bindings);
                                           depth = (uu___178_20069.depth);
                                           tcenv = tcenv';
                                           warn = (uu___178_20069.warn);
                                           cache = (uu___178_20069.cache);
                                           nolabels =
                                             (uu___178_20069.nolabels);
                                           use_zfuel_name =
                                             (uu___178_20069.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___178_20069.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___178_20069.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20011 with
                             | (env',e1,t_norm1) ->
                                 let uu____20079 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20079 with
                                  | ((binders,body,uu____20100,uu____20101),curry)
                                      ->
                                      ((let uu____20112 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20112
                                        then
                                          let uu____20113 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20114 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20113 uu____20114
                                        else ());
                                       (let uu____20116 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20116 with
                                        | (vars,guards,env'1,binder_decls,uu____20143)
                                            ->
                                            let body1 =
                                              let uu____20157 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20157
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20160 =
                                              let uu____20169 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20169
                                              then
                                                let uu____20180 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20181 =
                                                  encode_formula body1 env'1 in
                                                (uu____20180, uu____20181)
                                              else
                                                (let uu____20191 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20191)) in
                                            (match uu____20160 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20214 =
                                                     let uu____20221 =
                                                       let uu____20222 =
                                                         let uu____20233 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20233) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20222 in
                                                     let uu____20244 =
                                                       let uu____20247 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20247 in
                                                     (uu____20221,
                                                       uu____20244,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20214 in
                                                 let uu____20250 =
                                                   let uu____20253 =
                                                     let uu____20256 =
                                                       let uu____20259 =
                                                         let uu____20262 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20262 in
                                                       FStar_List.append
                                                         decls2 uu____20259 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20256 in
                                                   FStar_List.append decls1
                                                     uu____20253 in
                                                 (uu____20250, env2))))))
                        | uu____20267 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20352 = varops.fresh "fuel" in
                          (uu____20352, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20355 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20443  ->
                                  fun uu____20444  ->
                                    match (uu____20443, uu____20444) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20592 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20592 in
                                        let gtok =
                                          let uu____20594 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20594 in
                                        let env4 =
                                          let uu____20596 =
                                            let uu____20599 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20599 in
                                          push_free_var env3 flid gtok
                                            uu____20596 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20355 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20755 t_norm
                              uu____20757 =
                              match (uu____20755, uu____20757) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20801;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20802;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20830 =
                                    let uu____20837 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20837 with
                                    | (tcenv',uu____20859,e_t) ->
                                        let uu____20865 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20876 ->
                                              failwith "Impossible" in
                                        (match uu____20865 with
                                         | (e1,t_norm1) ->
                                             ((let uu___179_20892 = env3 in
                                               {
                                                 bindings =
                                                   (uu___179_20892.bindings);
                                                 depth =
                                                   (uu___179_20892.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___179_20892.warn);
                                                 cache =
                                                   (uu___179_20892.cache);
                                                 nolabels =
                                                   (uu___179_20892.nolabels);
                                                 use_zfuel_name =
                                                   (uu___179_20892.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___179_20892.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___179_20892.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20830 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20907 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20907
                                         then
                                           let uu____20908 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20909 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20910 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20908 uu____20909
                                             uu____20910
                                         else ());
                                        (let uu____20912 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20912 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20949 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20949
                                               then
                                                 let uu____20950 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20951 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20952 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20953 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20950 uu____20951
                                                   uu____20952 uu____20953
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20957 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20957 with
                                               | (vars,guards,env'1,binder_decls,uu____20988)
                                                   ->
                                                   let decl_g =
                                                     let uu____21002 =
                                                       let uu____21013 =
                                                         let uu____21016 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21016 in
                                                       (g, uu____21013,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21002 in
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
                                                     let uu____21041 =
                                                       let uu____21048 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21048) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21041 in
                                                   let gsapp =
                                                     let uu____21058 =
                                                       let uu____21065 =
                                                         let uu____21068 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21068 ::
                                                           vars_tm in
                                                       (g, uu____21065) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21058 in
                                                   let gmax =
                                                     let uu____21074 =
                                                       let uu____21081 =
                                                         let uu____21084 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21084 ::
                                                           vars_tm in
                                                       (g, uu____21081) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21074 in
                                                   let body1 =
                                                     let uu____21090 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21090
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21092 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21092 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21110 =
                                                            let uu____21117 =
                                                              let uu____21118
                                                                =
                                                                let uu____21133
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
                                                                  uu____21133) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21118 in
                                                            let uu____21154 =
                                                              let uu____21157
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21157 in
                                                            (uu____21117,
                                                              uu____21154,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21110 in
                                                        let eqn_f =
                                                          let uu____21161 =
                                                            let uu____21168 =
                                                              let uu____21169
                                                                =
                                                                let uu____21180
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21180) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21169 in
                                                            (uu____21168,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21161 in
                                                        let eqn_g' =
                                                          let uu____21194 =
                                                            let uu____21201 =
                                                              let uu____21202
                                                                =
                                                                let uu____21213
                                                                  =
                                                                  let uu____21214
                                                                    =
                                                                    let uu____21219
                                                                    =
                                                                    let uu____21220
                                                                    =
                                                                    let uu____21227
                                                                    =
                                                                    let uu____21230
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21230
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21227) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21220 in
                                                                    (gsapp,
                                                                    uu____21219) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21214 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21213) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21202 in
                                                            (uu____21201,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21194 in
                                                        let uu____21253 =
                                                          let uu____21262 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21262
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21291)
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
                                                                  let uu____21316
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21316
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21321
                                                                  =
                                                                  let uu____21328
                                                                    =
                                                                    let uu____21329
                                                                    =
                                                                    let uu____21340
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21340) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21329 in
                                                                  (uu____21328,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21321 in
                                                              let uu____21361
                                                                =
                                                                let uu____21368
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21368
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21381
                                                                    =
                                                                    let uu____21384
                                                                    =
                                                                    let uu____21385
                                                                    =
                                                                    let uu____21392
                                                                    =
                                                                    let uu____21393
                                                                    =
                                                                    let uu____21404
                                                                    =
                                                                    let uu____21405
                                                                    =
                                                                    let uu____21410
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21410,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21405 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21404) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21393 in
                                                                    (uu____21392,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21385 in
                                                                    [uu____21384] in
                                                                    (d3,
                                                                    uu____21381) in
                                                              (match uu____21361
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21253
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
                            let uu____21475 =
                              let uu____21488 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21567  ->
                                   fun uu____21568  ->
                                     match (uu____21567, uu____21568) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21723 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21723 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21488 in
                            (match uu____21475 with
                             | (decls2,eqns,env01) ->
                                 let uu____21796 =
                                   let isDeclFun uu___145_21808 =
                                     match uu___145_21808 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21809 -> true
                                     | uu____21820 -> false in
                                   let uu____21821 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21821
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21796 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21861 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___146_21865  ->
                                 match uu___146_21865 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21866 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21872 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21872))) in
                      if uu____21861
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
                   let uu____21924 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21924
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
        let uu____21973 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21973 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21977 = encode_sigelt' env se in
      match uu____21977 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21993 =
                  let uu____21994 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21994 in
                [uu____21993]
            | uu____21995 ->
                let uu____21996 =
                  let uu____21999 =
                    let uu____22000 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22000 in
                  uu____21999 :: g in
                let uu____22001 =
                  let uu____22004 =
                    let uu____22005 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22005 in
                  [uu____22004] in
                FStar_List.append uu____21996 uu____22001 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22018 =
          let uu____22019 = FStar_Syntax_Subst.compress t in
          uu____22019.FStar_Syntax_Syntax.n in
        match uu____22018 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22023)) -> s = "opaque_to_smt"
        | uu____22024 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22029 =
          let uu____22030 = FStar_Syntax_Subst.compress t in
          uu____22030.FStar_Syntax_Syntax.n in
        match uu____22029 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22034)) -> s = "uninterpreted_by_smt"
        | uu____22035 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22040 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22045 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22048 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22051 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22066 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22070 =
            let uu____22071 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22071 Prims.op_Negation in
          if uu____22070
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22097 ->
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
               let uu____22117 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22117 with
               | (aname,atok,env2) ->
                   let uu____22133 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22133 with
                    | (formals,uu____22151) ->
                        let uu____22164 =
                          let uu____22169 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22169 env2 in
                        (match uu____22164 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22181 =
                                 let uu____22182 =
                                   let uu____22193 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22209  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22193,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22182 in
                               [uu____22181;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22222 =
                               let aux uu____22274 uu____22275 =
                                 match (uu____22274, uu____22275) with
                                 | ((bv,uu____22327),(env3,acc_sorts,acc)) ->
                                     let uu____22365 = gen_term_var env3 bv in
                                     (match uu____22365 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22222 with
                              | (uu____22437,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22460 =
                                      let uu____22467 =
                                        let uu____22468 =
                                          let uu____22479 =
                                            let uu____22480 =
                                              let uu____22485 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22485) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22480 in
                                          ([[app]], xs_sorts, uu____22479) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22468 in
                                      (uu____22467,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22460 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22505 =
                                      let uu____22512 =
                                        let uu____22513 =
                                          let uu____22524 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22524) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22513 in
                                      (uu____22512,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22505 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22543 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22543 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22571,uu____22572)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22573 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22573 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22590,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22596 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___147_22600  ->
                      match uu___147_22600 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22601 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22606 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22607 -> false)) in
            Prims.op_Negation uu____22596 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22616 =
               let uu____22623 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22623 env fv t quals in
             match uu____22616 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22638 =
                   let uu____22641 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22641 in
                 (uu____22638, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22649 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22649 with
           | (uu____22658,f1) ->
               let uu____22660 = encode_formula f1 env in
               (match uu____22660 with
                | (f2,decls) ->
                    let g =
                      let uu____22674 =
                        let uu____22675 =
                          let uu____22682 =
                            let uu____22685 =
                              let uu____22686 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22686 in
                            FStar_Pervasives_Native.Some uu____22685 in
                          let uu____22687 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22682, uu____22687) in
                        FStar_SMTEncoding_Util.mkAssume uu____22675 in
                      [uu____22674] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22693) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22705 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22723 =
                       let uu____22726 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22726.FStar_Syntax_Syntax.fv_name in
                     uu____22723.FStar_Syntax_Syntax.v in
                   let uu____22727 =
                     let uu____22728 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22728 in
                   if uu____22727
                   then
                     let val_decl =
                       let uu___182_22756 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___182_22756.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___182_22756.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___182_22756.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22761 = encode_sigelt' env1 val_decl in
                     match uu____22761 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22705 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22789,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22791;
                          FStar_Syntax_Syntax.lbtyp = uu____22792;
                          FStar_Syntax_Syntax.lbeff = uu____22793;
                          FStar_Syntax_Syntax.lbdef = uu____22794;_}::[]),uu____22795)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22814 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22814 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22843 =
                   let uu____22846 =
                     let uu____22847 =
                       let uu____22854 =
                         let uu____22855 =
                           let uu____22866 =
                             let uu____22867 =
                               let uu____22872 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22872) in
                             FStar_SMTEncoding_Util.mkEq uu____22867 in
                           ([[b2t_x]], [xx], uu____22866) in
                         FStar_SMTEncoding_Util.mkForall uu____22855 in
                       (uu____22854,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22847 in
                   [uu____22846] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22843 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22905,uu____22906) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___148_22915  ->
                  match uu___148_22915 with
                  | FStar_Syntax_Syntax.Discriminator uu____22916 -> true
                  | uu____22917 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22920,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22931 =
                     let uu____22932 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22932.FStar_Ident.idText in
                   uu____22931 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___149_22936  ->
                     match uu___149_22936 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22937 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22941) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___150_22958  ->
                  match uu___150_22958 with
                  | FStar_Syntax_Syntax.Projector uu____22959 -> true
                  | uu____22964 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22967 = try_lookup_free_var env l in
          (match uu____22967 with
           | FStar_Pervasives_Native.Some uu____22974 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___183_22978 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___183_22978.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___183_22978.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___183_22978.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22985) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23003) ->
          let uu____23012 = encode_sigelts env ses in
          (match uu____23012 with
           | (g,env1) ->
               let uu____23029 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___151_23052  ->
                         match uu___151_23052 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23053;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23054;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23055;_}
                             -> false
                         | uu____23058 -> true)) in
               (match uu____23029 with
                | (g',inversions) ->
                    let uu____23073 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___152_23094  ->
                              match uu___152_23094 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23095 ->
                                  true
                              | uu____23106 -> false)) in
                    (match uu____23073 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23124,tps,k,uu____23127,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___153_23144  ->
                    match uu___153_23144 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23145 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23154 = c in
              match uu____23154 with
              | (name,args,uu____23159,uu____23160,uu____23161) ->
                  let uu____23166 =
                    let uu____23167 =
                      let uu____23178 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23195  ->
                                match uu____23195 with
                                | (uu____23202,sort,uu____23204) -> sort)) in
                      (name, uu____23178, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23167 in
                  [uu____23166]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23231 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23237 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23237 FStar_Option.isNone)) in
            if uu____23231
            then []
            else
              (let uu____23269 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23269 with
               | (xxsym,xx) ->
                   let uu____23278 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23317  ->
                             fun l  ->
                               match uu____23317 with
                               | (out,decls) ->
                                   let uu____23337 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23337 with
                                    | (uu____23348,data_t) ->
                                        let uu____23350 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23350 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23396 =
                                                 let uu____23397 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23397.FStar_Syntax_Syntax.n in
                                               match uu____23396 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23408,indices) ->
                                                   indices
                                               | uu____23430 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23454  ->
                                                         match uu____23454
                                                         with
                                                         | (x,uu____23460) ->
                                                             let uu____23461
                                                               =
                                                               let uu____23462
                                                                 =
                                                                 let uu____23469
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23469,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23462 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23461)
                                                    env) in
                                             let uu____23472 =
                                               encode_args indices env1 in
                                             (match uu____23472 with
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
                                                      let uu____23498 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23514
                                                                 =
                                                                 let uu____23519
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23519,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23514)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23498
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23522 =
                                                      let uu____23523 =
                                                        let uu____23528 =
                                                          let uu____23529 =
                                                            let uu____23534 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23534,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23529 in
                                                        (out, uu____23528) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23523 in
                                                    (uu____23522,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23278 with
                    | (data_ax,decls) ->
                        let uu____23547 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23547 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23558 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23558 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23562 =
                                 let uu____23569 =
                                   let uu____23570 =
                                     let uu____23581 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23596 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23581,
                                       uu____23596) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23570 in
                                 let uu____23611 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23569,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23611) in
                               FStar_SMTEncoding_Util.mkAssume uu____23562 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23614 =
            let uu____23627 =
              let uu____23628 = FStar_Syntax_Subst.compress k in
              uu____23628.FStar_Syntax_Syntax.n in
            match uu____23627 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23673 -> (tps, k) in
          (match uu____23614 with
           | (formals,res) ->
               let uu____23696 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23696 with
                | (formals1,res1) ->
                    let uu____23707 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23707 with
                     | (vars,guards,env',binder_decls,uu____23732) ->
                         let uu____23745 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23745 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23764 =
                                  let uu____23771 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23771) in
                                FStar_SMTEncoding_Util.mkApp uu____23764 in
                              let uu____23780 =
                                let tname_decl =
                                  let uu____23790 =
                                    let uu____23791 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23823  ->
                                              match uu____23823 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23836 = varops.next_id () in
                                    (tname, uu____23791,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23836, false) in
                                  constructor_or_logic_type_decl uu____23790 in
                                let uu____23845 =
                                  match vars with
                                  | [] ->
                                      let uu____23858 =
                                        let uu____23859 =
                                          let uu____23862 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23862 in
                                        push_free_var env1 t tname
                                          uu____23859 in
                                      ([], uu____23858)
                                  | uu____23869 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23878 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23878 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23892 =
                                          let uu____23899 =
                                            let uu____23900 =
                                              let uu____23915 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23915) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23900 in
                                          (uu____23899,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23892 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23845 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23780 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23955 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23955 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23973 =
                                               let uu____23974 =
                                                 let uu____23981 =
                                                   let uu____23982 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23982 in
                                                 (uu____23981,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23974 in
                                             [uu____23973]
                                           else [] in
                                         let uu____23986 =
                                           let uu____23989 =
                                             let uu____23992 =
                                               let uu____23993 =
                                                 let uu____24000 =
                                                   let uu____24001 =
                                                     let uu____24012 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24012) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24001 in
                                                 (uu____24000,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23993 in
                                             [uu____23992] in
                                           FStar_List.append karr uu____23989 in
                                         FStar_List.append decls1 uu____23986 in
                                   let aux =
                                     let uu____24028 =
                                       let uu____24031 =
                                         inversion_axioms tapp vars in
                                       let uu____24034 =
                                         let uu____24037 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24037] in
                                       FStar_List.append uu____24031
                                         uu____24034 in
                                     FStar_List.append kindingAx uu____24028 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24044,uu____24045,uu____24046,uu____24047,uu____24048)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24056,t,uu____24058,n_tps,uu____24060) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24068 = new_term_constant_and_tok_from_lid env d in
          (match uu____24068 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24085 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24085 with
                | (formals,t_res) ->
                    let uu____24120 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24120 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24134 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24134 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24204 =
                                            mk_term_projector_name d x in
                                          (uu____24204,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24206 =
                                  let uu____24225 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24225, true) in
                                FStar_All.pipe_right uu____24206
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
                              let uu____24264 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24264 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24276::uu____24277 ->
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
                                         let uu____24322 =
                                           let uu____24333 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24333) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24322
                                     | uu____24358 -> tok_typing in
                                   let uu____24367 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24367 with
                                    | (vars',guards',env'',decls_formals,uu____24392)
                                        ->
                                        let uu____24405 =
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
                                        (match uu____24405 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24436 ->
                                                   let uu____24443 =
                                                     let uu____24444 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24444 in
                                                   [uu____24443] in
                                             let encode_elim uu____24454 =
                                               let uu____24455 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24455 with
                                               | (head1,args) ->
                                                   let uu____24498 =
                                                     let uu____24499 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24499.FStar_Syntax_Syntax.n in
                                                   (match uu____24498 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24509;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24510;_},uu____24511)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24517 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24517
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
                                                                 | uu____24560
                                                                    ->
                                                                    let uu____24561
                                                                    =
                                                                    let uu____24562
                                                                    =
                                                                    let uu____24567
                                                                    =
                                                                    let uu____24568
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24568 in
                                                                    (uu____24567,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24562 in
                                                                    FStar_Exn.raise
                                                                    uu____24561 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24584
                                                                    =
                                                                    let uu____24585
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24585 in
                                                                    if
                                                                    uu____24584
                                                                    then
                                                                    let uu____24598
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24598]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24600
                                                               =
                                                               let uu____24613
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24663
                                                                     ->
                                                                    fun
                                                                    uu____24664
                                                                     ->
                                                                    match 
                                                                    (uu____24663,
                                                                    uu____24664)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24759
                                                                    =
                                                                    let uu____24766
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24766 in
                                                                    (match uu____24759
                                                                    with
                                                                    | 
                                                                    (uu____24779,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24787
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24787
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24789
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
                                                                 uu____24613 in
                                                             (match uu____24600
                                                              with
                                                              | (uu____24804,arg_vars,elim_eqns_or_guards,uu____24807)
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
                                                                    let uu____24837
                                                                    =
                                                                    let uu____24844
                                                                    =
                                                                    let uu____24845
                                                                    =
                                                                    let uu____24856
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24867
                                                                    =
                                                                    let uu____24868
                                                                    =
                                                                    let uu____24873
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24873) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24868 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24856,
                                                                    uu____24867) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24845 in
                                                                    (uu____24844,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24837 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24896
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24896,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24898
                                                                    =
                                                                    let uu____24905
                                                                    =
                                                                    let uu____24906
                                                                    =
                                                                    let uu____24917
                                                                    =
                                                                    let uu____24922
                                                                    =
                                                                    let uu____24925
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24925] in
                                                                    [uu____24922] in
                                                                    let uu____24930
                                                                    =
                                                                    let uu____24931
                                                                    =
                                                                    let uu____24936
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24937
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24936,
                                                                    uu____24937) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24931 in
                                                                    (uu____24917,
                                                                    [x],
                                                                    uu____24930) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24906 in
                                                                    let uu____24956
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24905,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24956) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24898
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24963
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
                                                                    (let uu____24991
                                                                    =
                                                                    let uu____24992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24992
                                                                    dapp1 in
                                                                    [uu____24991]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24963
                                                                    FStar_List.flatten in
                                                                    let uu____24999
                                                                    =
                                                                    let uu____25006
                                                                    =
                                                                    let uu____25007
                                                                    =
                                                                    let uu____25018
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25029
                                                                    =
                                                                    let uu____25030
                                                                    =
                                                                    let uu____25035
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25035) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25030 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25018,
                                                                    uu____25029) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25007 in
                                                                    (uu____25006,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24999) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25056 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25056
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
                                                                 | uu____25099
                                                                    ->
                                                                    let uu____25100
                                                                    =
                                                                    let uu____25101
                                                                    =
                                                                    let uu____25106
                                                                    =
                                                                    let uu____25107
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25107 in
                                                                    (uu____25106,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25101 in
                                                                    FStar_Exn.raise
                                                                    uu____25100 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25123
                                                                    =
                                                                    let uu____25124
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25124 in
                                                                    if
                                                                    uu____25123
                                                                    then
                                                                    let uu____25137
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25137]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25139
                                                               =
                                                               let uu____25152
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25202
                                                                     ->
                                                                    fun
                                                                    uu____25203
                                                                     ->
                                                                    match 
                                                                    (uu____25202,
                                                                    uu____25203)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25298
                                                                    =
                                                                    let uu____25305
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25305 in
                                                                    (match uu____25298
                                                                    with
                                                                    | 
                                                                    (uu____25318,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25326
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25326
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25328
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25328
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
                                                                 uu____25152 in
                                                             (match uu____25139
                                                              with
                                                              | (uu____25343,arg_vars,elim_eqns_or_guards,uu____25346)
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
                                                                    let uu____25376
                                                                    =
                                                                    let uu____25383
                                                                    =
                                                                    let uu____25384
                                                                    =
                                                                    let uu____25395
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25406
                                                                    =
                                                                    let uu____25407
                                                                    =
                                                                    let uu____25412
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25412) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25407 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25395,
                                                                    uu____25406) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25384 in
                                                                    (uu____25383,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25376 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25435
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25435,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25437
                                                                    =
                                                                    let uu____25444
                                                                    =
                                                                    let uu____25445
                                                                    =
                                                                    let uu____25456
                                                                    =
                                                                    let uu____25461
                                                                    =
                                                                    let uu____25464
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25464] in
                                                                    [uu____25461] in
                                                                    let uu____25469
                                                                    =
                                                                    let uu____25470
                                                                    =
                                                                    let uu____25475
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25476
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25475,
                                                                    uu____25476) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25470 in
                                                                    (uu____25456,
                                                                    [x],
                                                                    uu____25469) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25445 in
                                                                    let uu____25495
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25444,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25495) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25437
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25502
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
                                                                    (let uu____25530
                                                                    =
                                                                    let uu____25531
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25531
                                                                    dapp1 in
                                                                    [uu____25530]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25502
                                                                    FStar_List.flatten in
                                                                    let uu____25538
                                                                    =
                                                                    let uu____25545
                                                                    =
                                                                    let uu____25546
                                                                    =
                                                                    let uu____25557
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25568
                                                                    =
                                                                    let uu____25569
                                                                    =
                                                                    let uu____25574
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25574) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25569 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25557,
                                                                    uu____25568) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25546 in
                                                                    (uu____25545,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25538) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25593 ->
                                                        ((let uu____25595 =
                                                            let uu____25596 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25597 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25596
                                                              uu____25597 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25595);
                                                         ([], []))) in
                                             let uu____25602 = encode_elim () in
                                             (match uu____25602 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25622 =
                                                      let uu____25625 =
                                                        let uu____25628 =
                                                          let uu____25631 =
                                                            let uu____25634 =
                                                              let uu____25635
                                                                =
                                                                let uu____25646
                                                                  =
                                                                  let uu____25649
                                                                    =
                                                                    let uu____25650
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25650 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25649 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25646) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25635 in
                                                            [uu____25634] in
                                                          let uu____25655 =
                                                            let uu____25658 =
                                                              let uu____25661
                                                                =
                                                                let uu____25664
                                                                  =
                                                                  let uu____25667
                                                                    =
                                                                    let uu____25670
                                                                    =
                                                                    let uu____25673
                                                                    =
                                                                    let uu____25674
                                                                    =
                                                                    let uu____25681
                                                                    =
                                                                    let uu____25682
                                                                    =
                                                                    let uu____25693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25693) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25682 in
                                                                    (uu____25681,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25674 in
                                                                    let uu____25706
                                                                    =
                                                                    let uu____25709
                                                                    =
                                                                    let uu____25710
                                                                    =
                                                                    let uu____25717
                                                                    =
                                                                    let uu____25718
                                                                    =
                                                                    let uu____25729
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25729,
                                                                    uu____25740) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25718 in
                                                                    (uu____25717,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25710 in
                                                                    [uu____25709] in
                                                                    uu____25673
                                                                    ::
                                                                    uu____25706 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25670 in
                                                                  FStar_List.append
                                                                    uu____25667
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25664 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25661 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25658 in
                                                          FStar_List.append
                                                            uu____25631
                                                            uu____25655 in
                                                        FStar_List.append
                                                          decls3 uu____25628 in
                                                      FStar_List.append
                                                        decls2 uu____25625 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25622 in
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
           (fun uu____25786  ->
              fun se  ->
                match uu____25786 with
                | (g,env1) ->
                    let uu____25806 = encode_sigelt env1 se in
                    (match uu____25806 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25865 =
        match uu____25865 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25897 ->
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
                 ((let uu____25903 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25903
                   then
                     let uu____25904 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25905 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25906 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25904 uu____25905 uu____25906
                   else ());
                  (let uu____25908 = encode_term t1 env1 in
                   match uu____25908 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25924 =
                         let uu____25931 =
                           let uu____25932 =
                             let uu____25933 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25933
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25932 in
                         new_term_constant_from_string env1 x uu____25931 in
                       (match uu____25924 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25949 = FStar_Options.log_queries () in
                              if uu____25949
                              then
                                let uu____25952 =
                                  let uu____25953 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25954 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25955 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25953 uu____25954 uu____25955 in
                                FStar_Pervasives_Native.Some uu____25952
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25971,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25985 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25985 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26008,se,uu____26010) ->
                 let uu____26015 = encode_sigelt env1 se in
                 (match uu____26015 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26032,se) ->
                 let uu____26038 = encode_sigelt env1 se in
                 (match uu____26038 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26055 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26055 with | (uu____26078,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26093 'Auu____26094 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26094,'Auu____26093)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26162  ->
              match uu____26162 with
              | (l,uu____26174,uu____26175) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26221  ->
              match uu____26221 with
              | (l,uu____26235,uu____26236) ->
                  let uu____26245 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26246 =
                    let uu____26249 =
                      let uu____26250 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26250 in
                    [uu____26249] in
                  uu____26245 :: uu____26246)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26272 =
      let uu____26275 =
        let uu____26276 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26279 =
          let uu____26280 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26280 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26276;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26279
        } in
      [uu____26275] in
    FStar_ST.op_Colon_Equals last_env uu____26272
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26339 = FStar_ST.op_Bang last_env in
      match uu____26339 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26393 ->
          let uu___184_26396 = e in
          let uu____26397 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___184_26396.bindings);
            depth = (uu___184_26396.depth);
            tcenv;
            warn = (uu___184_26396.warn);
            cache = (uu___184_26396.cache);
            nolabels = (uu___184_26396.nolabels);
            use_zfuel_name = (uu___184_26396.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___184_26396.encode_non_total_function_typ);
            current_module_name = uu____26397
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26402 = FStar_ST.op_Bang last_env in
    match uu____26402 with
    | [] -> failwith "Empty env stack"
    | uu____26455::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26512  ->
    let uu____26513 = FStar_ST.op_Bang last_env in
    match uu____26513 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___185_26574 = hd1 in
          {
            bindings = (uu___185_26574.bindings);
            depth = (uu___185_26574.depth);
            tcenv = (uu___185_26574.tcenv);
            warn = (uu___185_26574.warn);
            cache = refs;
            nolabels = (uu___185_26574.nolabels);
            use_zfuel_name = (uu___185_26574.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___185_26574.encode_non_total_function_typ);
            current_module_name = (uu___185_26574.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26628  ->
    let uu____26629 = FStar_ST.op_Bang last_env in
    match uu____26629 with
    | [] -> failwith "Popping an empty stack"
    | uu____26682::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26780::uu____26781,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___186_26789 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___186_26789.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___186_26789.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___186_26789.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26790 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26807 =
        let uu____26810 =
          let uu____26811 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26811 in
        let uu____26812 = open_fact_db_tags env in uu____26810 :: uu____26812 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26807
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
      let uu____26836 = encode_sigelt env se in
      match uu____26836 with
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
        let uu____26874 = FStar_Options.log_queries () in
        if uu____26874
        then
          let uu____26877 =
            let uu____26878 =
              let uu____26879 =
                let uu____26880 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26880 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26879 in
            FStar_SMTEncoding_Term.Caption uu____26878 in
          uu____26877 :: decls
        else decls in
      (let uu____26891 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26891
       then
         let uu____26892 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26892
       else ());
      (let env =
         let uu____26895 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26895 tcenv in
       let uu____26896 = encode_top_level_facts env se in
       match uu____26896 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26910 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26910)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26924 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26924
       then
         let uu____26925 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26925
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26960  ->
                 fun se  ->
                   match uu____26960 with
                   | (g,env2) ->
                       let uu____26980 = encode_top_level_facts env2 se in
                       (match uu____26980 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27003 =
         encode_signature
           (let uu___187_27012 = env in
            {
              bindings = (uu___187_27012.bindings);
              depth = (uu___187_27012.depth);
              tcenv = (uu___187_27012.tcenv);
              warn = false;
              cache = (uu___187_27012.cache);
              nolabels = (uu___187_27012.nolabels);
              use_zfuel_name = (uu___187_27012.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___187_27012.encode_non_total_function_typ);
              current_module_name = (uu___187_27012.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27003 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27029 = FStar_Options.log_queries () in
             if uu____27029
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___188_27037 = env1 in
               {
                 bindings = (uu___188_27037.bindings);
                 depth = (uu___188_27037.depth);
                 tcenv = (uu___188_27037.tcenv);
                 warn = true;
                 cache = (uu___188_27037.cache);
                 nolabels = (uu___188_27037.nolabels);
                 use_zfuel_name = (uu___188_27037.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___188_27037.encode_non_total_function_typ);
                 current_module_name = (uu___188_27037.current_module_name)
               });
            (let uu____27039 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27039
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
        (let uu____27094 =
           let uu____27095 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27095.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27094);
        (let env =
           let uu____27097 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27097 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27109 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27144 = aux rest in
                 (match uu____27144 with
                  | (out,rest1) ->
                      let t =
                        let uu____27174 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27174 with
                        | FStar_Pervasives_Native.Some uu____27179 ->
                            let uu____27180 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27180
                              x.FStar_Syntax_Syntax.sort
                        | uu____27181 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27185 =
                        let uu____27188 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___189_27191 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___189_27191.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___189_27191.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27188 :: out in
                      (uu____27185, rest1))
             | uu____27196 -> ([], bindings1) in
           let uu____27203 = aux bindings in
           match uu____27203 with
           | (closing,bindings1) ->
               let uu____27228 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27228, bindings1) in
         match uu____27109 with
         | (q1,bindings1) ->
             let uu____27251 =
               let uu____27256 =
                 FStar_List.filter
                   (fun uu___154_27261  ->
                      match uu___154_27261 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27262 ->
                          false
                      | uu____27269 -> true) bindings1 in
               encode_env_bindings env uu____27256 in
             (match uu____27251 with
              | (env_decls,env1) ->
                  ((let uu____27287 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27287
                    then
                      let uu____27288 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27288
                    else ());
                   (let uu____27290 = encode_formula q1 env1 in
                    match uu____27290 with
                    | (phi,qdecls) ->
                        let uu____27311 =
                          let uu____27316 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27316 phi in
                        (match uu____27311 with
                         | (labels,phi1) ->
                             let uu____27333 = encode_labels labels in
                             (match uu____27333 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27370 =
                                      let uu____27377 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27378 =
                                        varops.mk_unique "@query" in
                                      (uu____27377,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27378) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27370 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))