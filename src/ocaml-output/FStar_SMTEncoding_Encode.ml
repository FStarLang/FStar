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
      (fun uu___124_119  ->
         match uu___124_119 with
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
        let uu___147_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___147_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___147_221.FStar_Syntax_Syntax.sort)
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
    let uu___148_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___148_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___148_1896.FStar_Syntax_Syntax.sort)
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
                 (fun uu___125_2369  ->
                    match uu___125_2369 with
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
           (fun uu___126_2394  ->
              match uu___126_2394 with
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
        (let uu___149_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___149_2483.tcenv);
           warn = (uu___149_2483.warn);
           cache = (uu___149_2483.cache);
           nolabels = (uu___149_2483.nolabels);
           use_zfuel_name = (uu___149_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___149_2483.encode_non_total_function_typ);
           current_module_name = (uu___149_2483.current_module_name)
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
        (let uu___150_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___150_2503.depth);
           tcenv = (uu___150_2503.tcenv);
           warn = (uu___150_2503.warn);
           cache = (uu___150_2503.cache);
           nolabels = (uu___150_2503.nolabels);
           use_zfuel_name = (uu___150_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___150_2503.encode_non_total_function_typ);
           current_module_name = (uu___150_2503.current_module_name)
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
          (let uu___151_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___151_2527.depth);
             tcenv = (uu___151_2527.tcenv);
             warn = (uu___151_2527.warn);
             cache = (uu___151_2527.cache);
             nolabels = (uu___151_2527.nolabels);
             use_zfuel_name = (uu___151_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___151_2527.encode_non_total_function_typ);
             current_module_name = (uu___151_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___152_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___152_2540.depth);
          tcenv = (uu___152_2540.tcenv);
          warn = (uu___152_2540.warn);
          cache = (uu___152_2540.cache);
          nolabels = (uu___152_2540.nolabels);
          use_zfuel_name = (uu___152_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___152_2540.encode_non_total_function_typ);
          current_module_name = (uu___152_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___127_2566  ->
             match uu___127_2566 with
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
        let uu___153_2639 = env in
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
          depth = (uu___153_2639.depth);
          tcenv = (uu___153_2639.tcenv);
          warn = (uu___153_2639.warn);
          cache = (uu___153_2639.cache);
          nolabels = (uu___153_2639.nolabels);
          use_zfuel_name = (uu___153_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___153_2639.encode_non_total_function_typ);
          current_module_name = (uu___153_2639.current_module_name)
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
        (fun uu___128_2704  ->
           match uu___128_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___129_2770  ->
             match uu___129_2770 with
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
          let uu___154_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___154_2892.depth);
            tcenv = (uu___154_2892.tcenv);
            warn = (uu___154_2892.warn);
            cache = (uu___154_2892.cache);
            nolabels = (uu___154_2892.nolabels);
            use_zfuel_name = (uu___154_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_2892.encode_non_total_function_typ);
            current_module_name = (uu___154_2892.current_module_name)
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
            let uu___155_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___155_2947.depth);
              tcenv = (uu___155_2947.tcenv);
              warn = (uu___155_2947.warn);
              cache = (uu___155_2947.cache);
              nolabels = (uu___155_2947.nolabels);
              use_zfuel_name = (uu___155_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___155_2947.encode_non_total_function_typ);
              current_module_name = (uu___155_2947.current_module_name)
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
        (fun uu___130_3201  ->
           match uu___130_3201 with
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
               (fun uu___131_3528  ->
                  match uu___131_3528 with
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
  fun uu___132_3636  ->
    match uu___132_3636 with
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
                           (let uu___156_6332 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___156_6332.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___156_6332.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___156_6332.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___156_6332.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___156_6332.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___156_6332.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___156_6332.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___156_6332.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___156_6332.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___156_6332.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___156_6332.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___156_6332.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___156_6332.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___156_6332.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___156_6332.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___156_6332.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___156_6332.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___156_6332.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___156_6332.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___156_6332.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___156_6332.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___156_6332.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___156_6332.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___156_6332.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___156_6332.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___156_6332.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___156_6332.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___156_6332.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___156_6332.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___156_6332.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___156_6332.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___156_6332.FStar_TypeChecker_Env.dsenv)
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
                 [FStar_TypeChecker_Normalize.WHNF;
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
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7077 =
                                             let uu____7084 =
                                               let uu____7085 =
                                                 let uu____7096 =
                                                   let uu____7097 =
                                                     let uu____7102 =
                                                       let uu____7103 =
                                                         let uu____7114 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7114) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7103 in
                                                     (uu____7102, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7097 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7096) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7085 in
                                             (uu____7084,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7077 in
                                         let t_kinding =
                                           let uu____7152 =
                                             let uu____7159 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7159,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7152 in
                                         let t_interp =
                                           let uu____7177 =
                                             let uu____7184 =
                                               let uu____7185 =
                                                 let uu____7196 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7196) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7185 in
                                             let uu____7219 =
                                               let uu____7222 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7222 in
                                             (uu____7184, uu____7219,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7177 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7229 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7229);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7259 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7259 in
           let uu____7260 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7260 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7272 =
                    let uu____7279 =
                      let uu____7280 =
                        let uu____7281 =
                          let uu____7282 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7282 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7281 in
                      varops.mk_unique uu____7280 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7279) in
                  FStar_SMTEncoding_Util.mkAssume uu____7272 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7287 ->
           let uu____7302 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7302 with
            | (head1,args_e) ->
                let uu____7343 =
                  let uu____7356 =
                    let uu____7357 = FStar_Syntax_Subst.compress head1 in
                    uu____7357.FStar_Syntax_Syntax.n in
                  (uu____7356, args_e) in
                (match uu____7343 with
                 | uu____7372 when head_redex env head1 ->
                     let uu____7385 = whnf env t in
                     encode_term uu____7385 env
                 | uu____7386 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7405 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7419;
                       FStar_Syntax_Syntax.vars = uu____7420;_},uu____7421),uu____7422::
                    (v1,uu____7424)::(v2,uu____7426)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7477 = encode_term v1 env in
                     (match uu____7477 with
                      | (v11,decls1) ->
                          let uu____7488 = encode_term v2 env in
                          (match uu____7488 with
                           | (v21,decls2) ->
                               let uu____7499 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7499,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7503::(v1,uu____7505)::(v2,uu____7507)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7554 = encode_term v1 env in
                     (match uu____7554 with
                      | (v11,decls1) ->
                          let uu____7565 = encode_term v2 env in
                          (match uu____7565 with
                           | (v21,decls2) ->
                               let uu____7576 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7576,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7579) ->
                     let e0 =
                       let uu____7597 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7597 in
                     ((let uu____7605 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7605
                       then
                         let uu____7606 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7606
                       else ());
                      (let e =
                         let uu____7611 =
                           let uu____7612 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7613 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7612
                             uu____7613 in
                         uu____7611 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7622),(arg,uu____7624)::[]) -> encode_term arg env
                 | uu____7649 ->
                     let uu____7662 = encode_args args_e env in
                     (match uu____7662 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7717 = encode_term head1 env in
                            match uu____7717 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7781 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7781 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7859  ->
                                                 fun uu____7860  ->
                                                   match (uu____7859,
                                                           uu____7860)
                                                   with
                                                   | ((bv,uu____7882),
                                                      (a,uu____7884)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7902 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7902
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7907 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7907 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7922 =
                                                   let uu____7929 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7938 =
                                                     let uu____7939 =
                                                       let uu____7940 =
                                                         let uu____7941 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7941 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7940 in
                                                     varops.mk_unique
                                                       uu____7939 in
                                                   (uu____7929,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7938) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7922 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7958 = lookup_free_var_sym env fv in
                            match uu____7958 with
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
                                   FStar_Syntax_Syntax.pos = uu____7989;
                                   FStar_Syntax_Syntax.vars = uu____7990;_},uu____7991)
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
                                   FStar_Syntax_Syntax.pos = uu____8002;
                                   FStar_Syntax_Syntax.vars = uu____8003;_},uu____8004)
                                ->
                                let uu____8009 =
                                  let uu____8010 =
                                    let uu____8015 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8015
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8010
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8009
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8045 =
                                  let uu____8046 =
                                    let uu____8051 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8051
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8046
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8045
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8080,(FStar_Util.Inl t1,uu____8082),uu____8083)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8132,(FStar_Util.Inr c,uu____8134),uu____8135)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8184 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8211 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8211 in
                               let uu____8212 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8212 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8228;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8229;_},uu____8230)
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
                                     | uu____8244 ->
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
           let uu____8293 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8293 with
            | (bs1,body1,opening) ->
                let fallback uu____8316 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8323 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8323, [decl]) in
                let is_impure rc =
                  let uu____8330 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8330 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8340 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8340
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8360 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8360
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8364 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8364)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8371 =
                         let uu____8372 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8372 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8371);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8374 =
                       (is_impure rc) &&
                         (let uu____8376 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8376) in
                     if uu____8374
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8383 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8383 with
                        | (vars,guards,envbody,decls,uu____8408) ->
                            let body2 =
                              let uu____8422 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8422
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8424 = encode_term body2 envbody in
                            (match uu____8424 with
                             | (body3,decls') ->
                                 let uu____8435 =
                                   let uu____8444 = codomain_eff rc in
                                   match uu____8444 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8463 = encode_term tfun env in
                                       (match uu____8463 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8435 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8495 =
                                          let uu____8506 =
                                            let uu____8507 =
                                              let uu____8512 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8512, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8507 in
                                          ([], vars, uu____8506) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8495 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8524 =
                                              let uu____8527 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8527
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8524 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8546 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8546 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8554 =
                                             let uu____8555 =
                                               let uu____8562 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8562) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8555 in
                                           (uu____8554,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8573 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8573 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8584 =
                                                    let uu____8585 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8585 = cache_size in
                                                  if uu____8584
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
                                                    let uu____8601 =
                                                      let uu____8602 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8602 in
                                                    varops.mk_unique
                                                      uu____8601 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8609 =
                                                    let uu____8616 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8616) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8609 in
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
                                                      let uu____8634 =
                                                        let uu____8635 =
                                                          let uu____8642 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8642,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8635 in
                                                      [uu____8634] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8655 =
                                                    let uu____8662 =
                                                      let uu____8663 =
                                                        let uu____8674 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8674) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8663 in
                                                    (uu____8662,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8655 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8691 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8691);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8694,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8695;
                          FStar_Syntax_Syntax.lbunivs = uu____8696;
                          FStar_Syntax_Syntax.lbtyp = uu____8697;
                          FStar_Syntax_Syntax.lbeff = uu____8698;
                          FStar_Syntax_Syntax.lbdef = uu____8699;_}::uu____8700),uu____8701)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8727;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8729;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8750 ->
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
              let uu____8820 = encode_term e1 env in
              match uu____8820 with
              | (ee1,decls1) ->
                  let uu____8831 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8831 with
                   | (xs,e21) ->
                       let uu____8856 = FStar_List.hd xs in
                       (match uu____8856 with
                        | (x1,uu____8870) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8872 = encode_body e21 env' in
                            (match uu____8872 with
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
            let uu____8904 =
              let uu____8911 =
                let uu____8912 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8912 in
              gen_term_var env uu____8911 in
            match uu____8904 with
            | (scrsym,scr',env1) ->
                let uu____8920 = encode_term e env1 in
                (match uu____8920 with
                 | (scr,decls) ->
                     let uu____8931 =
                       let encode_branch b uu____8956 =
                         match uu____8956 with
                         | (else_case,decls1) ->
                             let uu____8975 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8975 with
                              | (p,w,br) ->
                                  let uu____9001 = encode_pat env1 p in
                                  (match uu____9001 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9038  ->
                                                   match uu____9038 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9045 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9067 =
                                               encode_term w1 env2 in
                                             (match uu____9067 with
                                              | (w2,decls2) ->
                                                  let uu____9080 =
                                                    let uu____9081 =
                                                      let uu____9086 =
                                                        let uu____9087 =
                                                          let uu____9092 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9092) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9087 in
                                                      (guard, uu____9086) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9081 in
                                                  (uu____9080, decls2)) in
                                       (match uu____9045 with
                                        | (guard1,decls2) ->
                                            let uu____9105 =
                                              encode_br br env2 in
                                            (match uu____9105 with
                                             | (br1,decls3) ->
                                                 let uu____9118 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9118,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8931 with
                      | (match_tm,decls1) ->
                          let uu____9137 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9137, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9177 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9177
       then
         let uu____9178 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9178
       else ());
      (let uu____9180 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9180 with
       | (vars,pat_term) ->
           let uu____9197 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9250  ->
                     fun v1  ->
                       match uu____9250 with
                       | (env1,vars1) ->
                           let uu____9302 = gen_term_var env1 v1 in
                           (match uu____9302 with
                            | (xx,uu____9324,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9197 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9403 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9404 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9405 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9413 = encode_const c env1 in
                      (match uu____9413 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9427::uu____9428 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9431 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9454 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9454 with
                        | (uu____9461,uu____9462::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9465 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9498  ->
                                  match uu____9498 with
                                  | (arg,uu____9506) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9512 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9512)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9539) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9570 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9593 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9637  ->
                                  match uu____9637 with
                                  | (arg,uu____9651) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9657 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9657)) in
                      FStar_All.pipe_right uu____9593 FStar_List.flatten in
                let pat_term1 uu____9685 = encode_term pat_term env1 in
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
      let uu____9695 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9733  ->
                fun uu____9734  ->
                  match (uu____9733, uu____9734) with
                  | ((tms,decls),(t,uu____9770)) ->
                      let uu____9791 = encode_term t env in
                      (match uu____9791 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9695 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9848 = FStar_Syntax_Util.list_elements e in
        match uu____9848 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9869 =
          let uu____9884 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9884 FStar_Syntax_Util.head_and_args in
        match uu____9869 with
        | (head1,args) ->
            let uu____9923 =
              let uu____9936 =
                let uu____9937 = FStar_Syntax_Util.un_uinst head1 in
                uu____9937.FStar_Syntax_Syntax.n in
              (uu____9936, args) in
            (match uu____9923 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9951,uu____9952)::(e,uu____9954)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9989 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10025 =
            let uu____10040 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10040 FStar_Syntax_Util.head_and_args in
          match uu____10025 with
          | (head1,args) ->
              let uu____10081 =
                let uu____10094 =
                  let uu____10095 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10095.FStar_Syntax_Syntax.n in
                (uu____10094, args) in
              (match uu____10081 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10112)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10139 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10161 = smt_pat_or1 t1 in
            (match uu____10161 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10177 = list_elements1 e in
                 FStar_All.pipe_right uu____10177
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10195 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10195
                           (FStar_List.map one_pat)))
             | uu____10206 ->
                 let uu____10211 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10211])
        | uu____10232 ->
            let uu____10235 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10235] in
      let uu____10256 =
        let uu____10275 =
          let uu____10276 = FStar_Syntax_Subst.compress t in
          uu____10276.FStar_Syntax_Syntax.n in
        match uu____10275 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10315 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10315 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10358;
                        FStar_Syntax_Syntax.effect_name = uu____10359;
                        FStar_Syntax_Syntax.result_typ = uu____10360;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10362)::(post,uu____10364)::(pats,uu____10366)::[];
                        FStar_Syntax_Syntax.flags = uu____10367;_}
                      ->
                      let uu____10408 = lemma_pats pats in
                      (binders1, pre, post, uu____10408)
                  | uu____10425 -> failwith "impos"))
        | uu____10444 -> failwith "Impos" in
      match uu____10256 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___157_10492 = env in
            {
              bindings = (uu___157_10492.bindings);
              depth = (uu___157_10492.depth);
              tcenv = (uu___157_10492.tcenv);
              warn = (uu___157_10492.warn);
              cache = (uu___157_10492.cache);
              nolabels = (uu___157_10492.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___157_10492.encode_non_total_function_typ);
              current_module_name = (uu___157_10492.current_module_name)
            } in
          let uu____10493 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10493 with
           | (vars,guards,env2,decls,uu____10518) ->
               let uu____10531 =
                 let uu____10544 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10588 =
                             let uu____10597 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10597
                               FStar_List.unzip in
                           match uu____10588 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10544 FStar_List.unzip in
               (match uu____10531 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___158_10706 = env2 in
                      {
                        bindings = (uu___158_10706.bindings);
                        depth = (uu___158_10706.depth);
                        tcenv = (uu___158_10706.tcenv);
                        warn = (uu___158_10706.warn);
                        cache = (uu___158_10706.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___158_10706.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___158_10706.encode_non_total_function_typ);
                        current_module_name =
                          (uu___158_10706.current_module_name)
                      } in
                    let uu____10707 =
                      let uu____10712 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10712 env3 in
                    (match uu____10707 with
                     | (pre1,decls'') ->
                         let uu____10719 =
                           let uu____10724 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10724 env3 in
                         (match uu____10719 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10734 =
                                let uu____10735 =
                                  let uu____10746 =
                                    let uu____10747 =
                                      let uu____10752 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10752, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10747 in
                                  (pats, vars, uu____10746) in
                                FStar_SMTEncoding_Util.mkForall uu____10735 in
                              (uu____10734, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10771 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10771
        then
          let uu____10772 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10773 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10772 uu____10773
        else () in
      let enc f r l =
        let uu____10806 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10834 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10834 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10806 with
        | (decls,args) ->
            let uu____10863 =
              let uu___159_10864 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___159_10864.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___159_10864.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10863, decls) in
      let const_op f r uu____10895 =
        let uu____10908 = f r in (uu____10908, []) in
      let un_op f l =
        let uu____10927 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10927 in
      let bin_op f uu___133_10943 =
        match uu___133_10943 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10954 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10988 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11011  ->
                 match uu____11011 with
                 | (t,uu____11025) ->
                     let uu____11026 = encode_formula t env in
                     (match uu____11026 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10988 with
        | (decls,phis) ->
            let uu____11055 =
              let uu___160_11056 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_11056.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_11056.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11055, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11117  ->
               match uu____11117 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11136) -> false
                    | uu____11137 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11152 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11152
        else
          (let uu____11166 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11166 r rf) in
      let mk_imp1 r uu___134_11191 =
        match uu___134_11191 with
        | (lhs,uu____11197)::(rhs,uu____11199)::[] ->
            let uu____11226 = encode_formula rhs env in
            (match uu____11226 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11241) ->
                      (l1, decls1)
                  | uu____11246 ->
                      let uu____11247 = encode_formula lhs env in
                      (match uu____11247 with
                       | (l2,decls2) ->
                           let uu____11258 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11258, (FStar_List.append decls1 decls2)))))
        | uu____11261 -> failwith "impossible" in
      let mk_ite r uu___135_11282 =
        match uu___135_11282 with
        | (guard,uu____11288)::(_then,uu____11290)::(_else,uu____11292)::[]
            ->
            let uu____11329 = encode_formula guard env in
            (match uu____11329 with
             | (g,decls1) ->
                 let uu____11340 = encode_formula _then env in
                 (match uu____11340 with
                  | (t,decls2) ->
                      let uu____11351 = encode_formula _else env in
                      (match uu____11351 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11365 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11390 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11390 in
      let connectives =
        let uu____11408 =
          let uu____11421 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11421) in
        let uu____11438 =
          let uu____11453 =
            let uu____11466 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11466) in
          let uu____11483 =
            let uu____11498 =
              let uu____11513 =
                let uu____11526 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11526) in
              let uu____11543 =
                let uu____11558 =
                  let uu____11573 =
                    let uu____11586 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11586) in
                  [uu____11573;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11558 in
              uu____11513 :: uu____11543 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11498 in
          uu____11453 :: uu____11483 in
        uu____11408 :: uu____11438 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11907 = encode_formula phi' env in
            (match uu____11907 with
             | (phi2,decls) ->
                 let uu____11918 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11918, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11919 ->
            let uu____11926 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11926 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11965 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11965 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11977;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11979;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12000 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12000 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12047::(x,uu____12049)::(t,uu____12051)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12098 = encode_term x env in
                 (match uu____12098 with
                  | (x1,decls) ->
                      let uu____12109 = encode_term t env in
                      (match uu____12109 with
                       | (t1,decls') ->
                           let uu____12120 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12120, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12125)::(msg,uu____12127)::(phi2,uu____12129)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12174 =
                   let uu____12179 =
                     let uu____12180 = FStar_Syntax_Subst.compress r in
                     uu____12180.FStar_Syntax_Syntax.n in
                   let uu____12183 =
                     let uu____12184 = FStar_Syntax_Subst.compress msg in
                     uu____12184.FStar_Syntax_Syntax.n in
                   (uu____12179, uu____12183) in
                 (match uu____12174 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12193))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12199 -> fallback phi2)
             | uu____12204 when head_redex env head2 ->
                 let uu____12217 = whnf env phi1 in
                 encode_formula uu____12217 env
             | uu____12218 ->
                 let uu____12231 = encode_term phi1 env in
                 (match uu____12231 with
                  | (tt,decls) ->
                      let uu____12242 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___161_12245 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___161_12245.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___161_12245.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12242, decls)))
        | uu____12246 ->
            let uu____12247 = encode_term phi1 env in
            (match uu____12247 with
             | (tt,decls) ->
                 let uu____12258 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___162_12261 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___162_12261.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___162_12261.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12258, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12297 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12297 with
        | (vars,guards,env2,decls,uu____12336) ->
            let uu____12349 =
              let uu____12362 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12410 =
                          let uu____12419 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12449  ->
                                    match uu____12449 with
                                    | (t,uu____12459) ->
                                        encode_term t
                                          (let uu___163_12461 = env2 in
                                           {
                                             bindings =
                                               (uu___163_12461.bindings);
                                             depth = (uu___163_12461.depth);
                                             tcenv = (uu___163_12461.tcenv);
                                             warn = (uu___163_12461.warn);
                                             cache = (uu___163_12461.cache);
                                             nolabels =
                                               (uu___163_12461.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___163_12461.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___163_12461.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12419 FStar_List.unzip in
                        match uu____12410 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12362 FStar_List.unzip in
            (match uu____12349 with
             | (pats,decls') ->
                 let uu____12560 = encode_formula body env2 in
                 (match uu____12560 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12592;
                             FStar_SMTEncoding_Term.rng = uu____12593;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12608 -> guards in
                      let uu____12613 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12613, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12673  ->
                   match uu____12673 with
                   | (x,uu____12679) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12687 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12699 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12699) uu____12687 tl1 in
             let uu____12702 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12729  ->
                       match uu____12729 with
                       | (b,uu____12735) ->
                           let uu____12736 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12736)) in
             (match uu____12702 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12742) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12756 =
                    let uu____12757 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12757 in
                  FStar_Errors.warn pos uu____12756) in
       let uu____12758 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12758 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12767 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12825  ->
                     match uu____12825 with
                     | (l,uu____12839) -> FStar_Ident.lid_equals op l)) in
           (match uu____12767 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12872,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12912 = encode_q_body env vars pats body in
             match uu____12912 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12957 =
                     let uu____12968 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12968) in
                   FStar_SMTEncoding_Term.mkForall uu____12957
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12987 = encode_q_body env vars pats body in
             match uu____12987 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13031 =
                   let uu____13032 =
                     let uu____13043 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13043) in
                   FStar_SMTEncoding_Term.mkExists uu____13032
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13031, decls))))
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
  let uu____13141 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13141 with
  | (asym,a) ->
      let uu____13148 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13148 with
       | (xsym,x) ->
           let uu____13155 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13155 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13199 =
                      let uu____13210 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13210, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13199 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13236 =
                      let uu____13243 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13243) in
                    FStar_SMTEncoding_Util.mkApp uu____13236 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13256 =
                    let uu____13259 =
                      let uu____13262 =
                        let uu____13265 =
                          let uu____13266 =
                            let uu____13273 =
                              let uu____13274 =
                                let uu____13285 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13285) in
                              FStar_SMTEncoding_Util.mkForall uu____13274 in
                            (uu____13273, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13266 in
                        let uu____13302 =
                          let uu____13305 =
                            let uu____13306 =
                              let uu____13313 =
                                let uu____13314 =
                                  let uu____13325 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13325) in
                                FStar_SMTEncoding_Util.mkForall uu____13314 in
                              (uu____13313,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13306 in
                          [uu____13305] in
                        uu____13265 :: uu____13302 in
                      xtok_decl :: uu____13262 in
                    xname_decl :: uu____13259 in
                  (xtok1, uu____13256) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13416 =
                    let uu____13429 =
                      let uu____13438 =
                        let uu____13439 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13439 in
                      quant axy uu____13438 in
                    (FStar_Parser_Const.op_Eq, uu____13429) in
                  let uu____13448 =
                    let uu____13463 =
                      let uu____13476 =
                        let uu____13485 =
                          let uu____13486 =
                            let uu____13487 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13487 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13486 in
                        quant axy uu____13485 in
                      (FStar_Parser_Const.op_notEq, uu____13476) in
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
                              FStar_SMTEncoding_Util.mkLT uu____13535 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13534 in
                          quant xy uu____13533 in
                        (FStar_Parser_Const.op_LT, uu____13524) in
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
                                FStar_SMTEncoding_Util.mkLTE uu____13589 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13588 in
                            quant xy uu____13587 in
                          (FStar_Parser_Const.op_LTE, uu____13578) in
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
                                  FStar_SMTEncoding_Util.mkGT uu____13643 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13642 in
                              quant xy uu____13641 in
                            (FStar_Parser_Const.op_GT, uu____13632) in
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
                                    FStar_SMTEncoding_Util.mkGTE uu____13697 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13696 in
                                quant xy uu____13695 in
                              (FStar_Parser_Const.op_GTE, uu____13686) in
                            let uu____13712 =
                              let uu____13727 =
                                let uu____13740 =
                                  let uu____13749 =
                                    let uu____13750 =
                                      let uu____13751 =
                                        let uu____13756 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13757 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13756, uu____13757) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13751 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13750 in
                                  quant xy uu____13749 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13740) in
                              let uu____13766 =
                                let uu____13781 =
                                  let uu____13794 =
                                    let uu____13803 =
                                      let uu____13804 =
                                        let uu____13805 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13805 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13804 in
                                    quant qx uu____13803 in
                                  (FStar_Parser_Const.op_Minus, uu____13794) in
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
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13853 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13852 in
                                      quant xy uu____13851 in
                                    (FStar_Parser_Const.op_Addition,
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
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13907 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13906 in
                                        quant xy uu____13905 in
                                      (FStar_Parser_Const.op_Multiply,
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
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13961 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13960 in
                                          quant xy uu____13959 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13950) in
                                      let uu____13976 =
                                        let uu____13991 =
                                          let uu____14004 =
                                            let uu____14013 =
                                              let uu____14014 =
                                                let uu____14015 =
                                                  let uu____14020 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14021 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14020, uu____14021) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14015 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14014 in
                                            quant xy uu____14013 in
                                          (FStar_Parser_Const.op_Modulus,
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
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14069 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14068 in
                                              quant xy uu____14067 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14058) in
                                          let uu____14084 =
                                            let uu____14099 =
                                              let uu____14112 =
                                                let uu____14121 =
                                                  let uu____14122 =
                                                    let uu____14123 =
                                                      let uu____14128 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14129 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14128,
                                                        uu____14129) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14123 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14122 in
                                                quant xy uu____14121 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14112) in
                                            let uu____14138 =
                                              let uu____14153 =
                                                let uu____14166 =
                                                  let uu____14175 =
                                                    let uu____14176 =
                                                      let uu____14177 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14177 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14176 in
                                                  quant qx uu____14175 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14166) in
                                              [uu____14153] in
                                            uu____14099 :: uu____14138 in
                                          uu____14045 :: uu____14084 in
                                        uu____13991 :: uu____14030 in
                                      uu____13937 :: uu____13976 in
                                    uu____13883 :: uu____13922 in
                                  uu____13829 :: uu____13868 in
                                uu____13781 :: uu____13814 in
                              uu____13727 :: uu____13766 in
                            uu____13673 :: uu____13712 in
                          uu____13619 :: uu____13658 in
                        uu____13565 :: uu____13604 in
                      uu____13511 :: uu____13550 in
                    uu____13463 :: uu____13496 in
                  uu____13416 :: uu____13448 in
                let mk1 l v1 =
                  let uu____14391 =
                    let uu____14400 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14458  ->
                              match uu____14458 with
                              | (l',uu____14472) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14400
                      (FStar_Option.map
                         (fun uu____14532  ->
                            match uu____14532 with | (uu____14551,b) -> b v1)) in
                  FStar_All.pipe_right uu____14391 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14622  ->
                          match uu____14622 with
                          | (l',uu____14636) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14677 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14677 with
        | (xxsym,xx) ->
            let uu____14684 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14684 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14694 =
                   let uu____14701 =
                     let uu____14702 =
                       let uu____14713 =
                         let uu____14714 =
                           let uu____14719 =
                             let uu____14720 =
                               let uu____14725 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14725) in
                             FStar_SMTEncoding_Util.mkEq uu____14720 in
                           (xx_has_type, uu____14719) in
                         FStar_SMTEncoding_Util.mkImp uu____14714 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14713) in
                     FStar_SMTEncoding_Util.mkForall uu____14702 in
                   let uu____14750 =
                     let uu____14751 =
                       let uu____14752 =
                         let uu____14753 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14753 in
                       Prims.strcat module_name uu____14752 in
                     varops.mk_unique uu____14751 in
                   (uu____14701, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14750) in
                 FStar_SMTEncoding_Util.mkAssume uu____14694)
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
    let uu____14793 =
      let uu____14794 =
        let uu____14801 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14801, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14794 in
    let uu____14804 =
      let uu____14807 =
        let uu____14808 =
          let uu____14815 =
            let uu____14816 =
              let uu____14827 =
                let uu____14828 =
                  let uu____14833 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14833) in
                FStar_SMTEncoding_Util.mkImp uu____14828 in
              ([[typing_pred]], [xx], uu____14827) in
            mkForall_fuel uu____14816 in
          (uu____14815, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14808 in
      [uu____14807] in
    uu____14793 :: uu____14804 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14875 =
      let uu____14876 =
        let uu____14883 =
          let uu____14884 =
            let uu____14895 =
              let uu____14900 =
                let uu____14903 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14903] in
              [uu____14900] in
            let uu____14908 =
              let uu____14909 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14909 tt in
            (uu____14895, [bb], uu____14908) in
          FStar_SMTEncoding_Util.mkForall uu____14884 in
        (uu____14883, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14876 in
    let uu____14930 =
      let uu____14933 =
        let uu____14934 =
          let uu____14941 =
            let uu____14942 =
              let uu____14953 =
                let uu____14954 =
                  let uu____14959 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14959) in
                FStar_SMTEncoding_Util.mkImp uu____14954 in
              ([[typing_pred]], [xx], uu____14953) in
            mkForall_fuel uu____14942 in
          (uu____14941, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14934 in
      [uu____14933] in
    uu____14875 :: uu____14930 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15009 =
        let uu____15010 =
          let uu____15017 =
            let uu____15020 =
              let uu____15023 =
                let uu____15026 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15027 =
                  let uu____15030 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15030] in
                uu____15026 :: uu____15027 in
              tt :: uu____15023 in
            tt :: uu____15020 in
          ("Prims.Precedes", uu____15017) in
        FStar_SMTEncoding_Util.mkApp uu____15010 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15009 in
    let precedes_y_x =
      let uu____15034 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15034 in
    let uu____15037 =
      let uu____15038 =
        let uu____15045 =
          let uu____15046 =
            let uu____15057 =
              let uu____15062 =
                let uu____15065 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15065] in
              [uu____15062] in
            let uu____15070 =
              let uu____15071 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15071 tt in
            (uu____15057, [bb], uu____15070) in
          FStar_SMTEncoding_Util.mkForall uu____15046 in
        (uu____15045, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15038 in
    let uu____15092 =
      let uu____15095 =
        let uu____15096 =
          let uu____15103 =
            let uu____15104 =
              let uu____15115 =
                let uu____15116 =
                  let uu____15121 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15121) in
                FStar_SMTEncoding_Util.mkImp uu____15116 in
              ([[typing_pred]], [xx], uu____15115) in
            mkForall_fuel uu____15104 in
          (uu____15103, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15096 in
      let uu____15146 =
        let uu____15149 =
          let uu____15150 =
            let uu____15157 =
              let uu____15158 =
                let uu____15169 =
                  let uu____15170 =
                    let uu____15175 =
                      let uu____15176 =
                        let uu____15179 =
                          let uu____15182 =
                            let uu____15185 =
                              let uu____15186 =
                                let uu____15191 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15192 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15191, uu____15192) in
                              FStar_SMTEncoding_Util.mkGT uu____15186 in
                            let uu____15193 =
                              let uu____15196 =
                                let uu____15197 =
                                  let uu____15202 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15203 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15202, uu____15203) in
                                FStar_SMTEncoding_Util.mkGTE uu____15197 in
                              let uu____15204 =
                                let uu____15207 =
                                  let uu____15208 =
                                    let uu____15213 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15214 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15213, uu____15214) in
                                  FStar_SMTEncoding_Util.mkLT uu____15208 in
                                [uu____15207] in
                              uu____15196 :: uu____15204 in
                            uu____15185 :: uu____15193 in
                          typing_pred_y :: uu____15182 in
                        typing_pred :: uu____15179 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15176 in
                    (uu____15175, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15170 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15169) in
              mkForall_fuel uu____15158 in
            (uu____15157,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15150 in
        [uu____15149] in
      uu____15095 :: uu____15146 in
    uu____15037 :: uu____15092 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15260 =
      let uu____15261 =
        let uu____15268 =
          let uu____15269 =
            let uu____15280 =
              let uu____15285 =
                let uu____15288 = FStar_SMTEncoding_Term.boxString b in
                [uu____15288] in
              [uu____15285] in
            let uu____15293 =
              let uu____15294 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15294 tt in
            (uu____15280, [bb], uu____15293) in
          FStar_SMTEncoding_Util.mkForall uu____15269 in
        (uu____15268, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15261 in
    let uu____15315 =
      let uu____15318 =
        let uu____15319 =
          let uu____15326 =
            let uu____15327 =
              let uu____15338 =
                let uu____15339 =
                  let uu____15344 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15344) in
                FStar_SMTEncoding_Util.mkImp uu____15339 in
              ([[typing_pred]], [xx], uu____15338) in
            mkForall_fuel uu____15327 in
          (uu____15326, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15319 in
      [uu____15318] in
    uu____15260 :: uu____15315 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15397 =
      let uu____15398 =
        let uu____15405 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15405, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15398 in
    [uu____15397] in
  let mk_and_interp env conj uu____15417 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15442 =
      let uu____15443 =
        let uu____15450 =
          let uu____15451 =
            let uu____15462 =
              let uu____15463 =
                let uu____15468 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15468, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15463 in
            ([[l_and_a_b]], [aa; bb], uu____15462) in
          FStar_SMTEncoding_Util.mkForall uu____15451 in
        (uu____15450, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15443 in
    [uu____15442] in
  let mk_or_interp env disj uu____15506 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15531 =
      let uu____15532 =
        let uu____15539 =
          let uu____15540 =
            let uu____15551 =
              let uu____15552 =
                let uu____15557 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15557, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15552 in
            ([[l_or_a_b]], [aa; bb], uu____15551) in
          FStar_SMTEncoding_Util.mkForall uu____15540 in
        (uu____15539, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15532 in
    [uu____15531] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15620 =
      let uu____15621 =
        let uu____15628 =
          let uu____15629 =
            let uu____15640 =
              let uu____15641 =
                let uu____15646 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15646, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15641 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15640) in
          FStar_SMTEncoding_Util.mkForall uu____15629 in
        (uu____15628, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15621 in
    [uu____15620] in
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
    let uu____15719 =
      let uu____15720 =
        let uu____15727 =
          let uu____15728 =
            let uu____15739 =
              let uu____15740 =
                let uu____15745 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15745, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15740 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15739) in
          FStar_SMTEncoding_Util.mkForall uu____15728 in
        (uu____15727, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15720 in
    [uu____15719] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15816 =
      let uu____15817 =
        let uu____15824 =
          let uu____15825 =
            let uu____15836 =
              let uu____15837 =
                let uu____15842 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15842, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15837 in
            ([[l_imp_a_b]], [aa; bb], uu____15836) in
          FStar_SMTEncoding_Util.mkForall uu____15825 in
        (uu____15824, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15817 in
    [uu____15816] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15905 =
      let uu____15906 =
        let uu____15913 =
          let uu____15914 =
            let uu____15925 =
              let uu____15926 =
                let uu____15931 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15931, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15926 in
            ([[l_iff_a_b]], [aa; bb], uu____15925) in
          FStar_SMTEncoding_Util.mkForall uu____15914 in
        (uu____15913, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15906 in
    [uu____15905] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15983 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15983 in
    let uu____15986 =
      let uu____15987 =
        let uu____15994 =
          let uu____15995 =
            let uu____16006 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16006) in
          FStar_SMTEncoding_Util.mkForall uu____15995 in
        (uu____15994, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15987 in
    [uu____15986] in
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
      let uu____16066 =
        let uu____16073 =
          let uu____16076 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16076] in
        ("Valid", uu____16073) in
      FStar_SMTEncoding_Util.mkApp uu____16066 in
    let uu____16079 =
      let uu____16080 =
        let uu____16087 =
          let uu____16088 =
            let uu____16099 =
              let uu____16100 =
                let uu____16105 =
                  let uu____16106 =
                    let uu____16117 =
                      let uu____16122 =
                        let uu____16125 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16125] in
                      [uu____16122] in
                    let uu____16130 =
                      let uu____16131 =
                        let uu____16136 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16136, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16131 in
                    (uu____16117, [xx1], uu____16130) in
                  FStar_SMTEncoding_Util.mkForall uu____16106 in
                (uu____16105, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16100 in
            ([[l_forall_a_b]], [aa; bb], uu____16099) in
          FStar_SMTEncoding_Util.mkForall uu____16088 in
        (uu____16087, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16080 in
    [uu____16079] in
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
      let uu____16218 =
        let uu____16225 =
          let uu____16228 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16228] in
        ("Valid", uu____16225) in
      FStar_SMTEncoding_Util.mkApp uu____16218 in
    let uu____16231 =
      let uu____16232 =
        let uu____16239 =
          let uu____16240 =
            let uu____16251 =
              let uu____16252 =
                let uu____16257 =
                  let uu____16258 =
                    let uu____16269 =
                      let uu____16274 =
                        let uu____16277 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16277] in
                      [uu____16274] in
                    let uu____16282 =
                      let uu____16283 =
                        let uu____16288 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16288, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16283 in
                    (uu____16269, [xx1], uu____16282) in
                  FStar_SMTEncoding_Util.mkExists uu____16258 in
                (uu____16257, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16252 in
            ([[l_exists_a_b]], [aa; bb], uu____16251) in
          FStar_SMTEncoding_Util.mkForall uu____16240 in
        (uu____16239, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16232 in
    [uu____16231] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16348 =
      let uu____16349 =
        let uu____16356 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16357 = varops.mk_unique "typing_range_const" in
        (uu____16356, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16357) in
      FStar_SMTEncoding_Util.mkAssume uu____16349 in
    [uu____16348] in
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
        let uu____16391 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16391 x1 t in
      let uu____16392 =
        let uu____16403 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16403) in
      FStar_SMTEncoding_Util.mkForall uu____16392 in
    let uu____16426 =
      let uu____16427 =
        let uu____16434 =
          let uu____16435 =
            let uu____16446 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16446) in
          FStar_SMTEncoding_Util.mkForall uu____16435 in
        (uu____16434,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16427 in
    [uu____16426] in
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
          let uu____16770 =
            FStar_Util.find_opt
              (fun uu____16796  ->
                 match uu____16796 with
                 | (l,uu____16808) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16770 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16833,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16872 = encode_function_type_as_formula t env in
        match uu____16872 with
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
              let uu____16918 =
                ((let uu____16921 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16921) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16918
              then
                let uu____16928 = new_term_constant_and_tok_from_lid env lid in
                match uu____16928 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16947 =
                        let uu____16948 = FStar_Syntax_Subst.compress t_norm in
                        uu____16948.FStar_Syntax_Syntax.n in
                      match uu____16947 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16954) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16984  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16989 -> [] in
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
                (let uu____17003 = prims.is lid in
                 if uu____17003
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17011 = prims.mk lid vname in
                   match uu____17011 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17035 =
                      let uu____17046 = curried_arrow_formals_comp t_norm in
                      match uu____17046 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17064 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17064
                            then
                              let uu____17065 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___164_17068 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___164_17068.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___164_17068.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___164_17068.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___164_17068.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___164_17068.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___164_17068.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___164_17068.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___164_17068.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___164_17068.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___164_17068.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___164_17068.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___164_17068.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___164_17068.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___164_17068.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___164_17068.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___164_17068.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___164_17068.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___164_17068.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___164_17068.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___164_17068.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___164_17068.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___164_17068.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___164_17068.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___164_17068.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___164_17068.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___164_17068.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___164_17068.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___164_17068.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___164_17068.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___164_17068.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___164_17068.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___164_17068.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17065
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17080 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17080)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17035 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17125 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17125 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17146 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___136_17188  ->
                                       match uu___136_17188 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17192 =
                                             FStar_Util.prefix vars in
                                           (match uu____17192 with
                                            | (uu____17213,(xxsym,uu____17215))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17233 =
                                                  let uu____17234 =
                                                    let uu____17241 =
                                                      let uu____17242 =
                                                        let uu____17253 =
                                                          let uu____17254 =
                                                            let uu____17259 =
                                                              let uu____17260
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17260 in
                                                            (vapp,
                                                              uu____17259) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17254 in
                                                        ([[vapp]], vars,
                                                          uu____17253) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17242 in
                                                    (uu____17241,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17234 in
                                                [uu____17233])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17279 =
                                             FStar_Util.prefix vars in
                                           (match uu____17279 with
                                            | (uu____17300,(xxsym,uu____17302))
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
                                                let uu____17325 =
                                                  let uu____17326 =
                                                    let uu____17333 =
                                                      let uu____17334 =
                                                        let uu____17345 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17345) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17334 in
                                                    (uu____17333,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17326 in
                                                [uu____17325])
                                       | uu____17362 -> [])) in
                             let uu____17363 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17363 with
                              | (vars,guards,env',decls1,uu____17390) ->
                                  let uu____17403 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17412 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17412, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17414 =
                                          encode_formula p env' in
                                        (match uu____17414 with
                                         | (g,ds) ->
                                             let uu____17425 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17425,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17403 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17438 =
                                           let uu____17445 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17445) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17438 in
                                       let uu____17454 =
                                         let vname_decl =
                                           let uu____17462 =
                                             let uu____17473 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17483  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17473,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17462 in
                                         let uu____17492 =
                                           let env2 =
                                             let uu___165_17498 = env1 in
                                             {
                                               bindings =
                                                 (uu___165_17498.bindings);
                                               depth = (uu___165_17498.depth);
                                               tcenv = (uu___165_17498.tcenv);
                                               warn = (uu___165_17498.warn);
                                               cache = (uu___165_17498.cache);
                                               nolabels =
                                                 (uu___165_17498.nolabels);
                                               use_zfuel_name =
                                                 (uu___165_17498.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___165_17498.current_module_name)
                                             } in
                                           let uu____17499 =
                                             let uu____17500 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17500 in
                                           if uu____17499
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17492 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17515::uu____17516 ->
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
                                                     let uu____17556 =
                                                       let uu____17567 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17567) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17556 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17594 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17597 =
                                               match formals with
                                               | [] ->
                                                   let uu____17614 =
                                                     let uu____17615 =
                                                       let uu____17618 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17618 in
                                                     push_free_var env1 lid
                                                       vname uu____17615 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17614)
                                               | uu____17623 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17630 =
                                                       let uu____17637 =
                                                         let uu____17638 =
                                                           let uu____17649 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17649) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17638 in
                                                       (uu____17637,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17630 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17597 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17454 with
                                        | (decls2,env2) ->
                                            let uu____17692 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17700 =
                                                encode_term res_t1 env' in
                                              match uu____17700 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17713 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17713, decls) in
                                            (match uu____17692 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17724 =
                                                     let uu____17731 =
                                                       let uu____17732 =
                                                         let uu____17743 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17743) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17732 in
                                                     (uu____17731,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17724 in
                                                 let freshness =
                                                   let uu____17759 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17759
                                                   then
                                                     let uu____17764 =
                                                       let uu____17765 =
                                                         let uu____17776 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17787 =
                                                           varops.next_id () in
                                                         (vname, uu____17776,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17787) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17765 in
                                                     let uu____17790 =
                                                       let uu____17793 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17793] in
                                                     uu____17764 ::
                                                       uu____17790
                                                   else [] in
                                                 let g =
                                                   let uu____17798 =
                                                     let uu____17801 =
                                                       let uu____17804 =
                                                         let uu____17807 =
                                                           let uu____17810 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17810 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17807 in
                                                       FStar_List.append
                                                         decls3 uu____17804 in
                                                     FStar_List.append decls2
                                                       uu____17801 in
                                                   FStar_List.append decls11
                                                     uu____17798 in
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
          let uu____17845 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17845 with
          | FStar_Pervasives_Native.None  ->
              let uu____17882 = encode_free_var false env x t t_norm [] in
              (match uu____17882 with
               | (decls,env1) ->
                   let uu____17909 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17909 with
                    | (n1,x',uu____17936) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17957) ->
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
            let uu____18017 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18017 with
            | (decls,env1) ->
                let uu____18036 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18036
                then
                  let uu____18043 =
                    let uu____18046 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18046 in
                  (uu____18043, env1)
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
             (fun uu____18101  ->
                fun lb  ->
                  match uu____18101 with
                  | (decls,env1) ->
                      let uu____18121 =
                        let uu____18128 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18128
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18121 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18150 = FStar_Syntax_Util.head_and_args t in
    match uu____18150 with
    | (hd1,args) ->
        let uu____18187 =
          let uu____18188 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18188.FStar_Syntax_Syntax.n in
        (match uu____18187 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18192,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18211 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18236  ->
      fun quals  ->
        match uu____18236 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18312 = FStar_Util.first_N nbinders formals in
              match uu____18312 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18393  ->
                         fun uu____18394  ->
                           match (uu____18393, uu____18394) with
                           | ((formal,uu____18412),(binder,uu____18414)) ->
                               let uu____18423 =
                                 let uu____18430 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18430) in
                               FStar_Syntax_Syntax.NT uu____18423) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18438 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18469  ->
                              match uu____18469 with
                              | (x,i) ->
                                  let uu____18480 =
                                    let uu___166_18481 = x in
                                    let uu____18482 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___166_18481.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___166_18481.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18482
                                    } in
                                  (uu____18480, i))) in
                    FStar_All.pipe_right uu____18438
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18500 =
                      let uu____18501 = FStar_Syntax_Subst.compress body in
                      let uu____18502 =
                        let uu____18503 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18503 in
                      FStar_Syntax_Syntax.extend_app_n uu____18501
                        uu____18502 in
                    uu____18500 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18564 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18564
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___167_18567 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___167_18567.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___167_18567.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___167_18567.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___167_18567.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___167_18567.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___167_18567.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___167_18567.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___167_18567.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___167_18567.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___167_18567.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___167_18567.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___167_18567.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___167_18567.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___167_18567.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___167_18567.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___167_18567.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___167_18567.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___167_18567.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___167_18567.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___167_18567.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___167_18567.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___167_18567.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___167_18567.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___167_18567.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___167_18567.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___167_18567.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___167_18567.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___167_18567.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___167_18567.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___167_18567.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___167_18567.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___167_18567.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18600 = FStar_Syntax_Util.abs_formals e in
                match uu____18600 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18664::uu____18665 ->
                         let uu____18680 =
                           let uu____18681 =
                             let uu____18684 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18684 in
                           uu____18681.FStar_Syntax_Syntax.n in
                         (match uu____18680 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18727 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18727 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18769 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18769
                                   then
                                     let uu____18804 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18804 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18898  ->
                                                   fun uu____18899  ->
                                                     match (uu____18898,
                                                             uu____18899)
                                                     with
                                                     | ((x,uu____18917),
                                                        (b,uu____18919)) ->
                                                         let uu____18928 =
                                                           let uu____18935 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18935) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18928)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18937 =
                                            let uu____18958 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18958) in
                                          (uu____18937, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19026 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19026 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19115) ->
                              let uu____19120 =
                                let uu____19141 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19141 in
                              (uu____19120, true)
                          | uu____19206 when Prims.op_Negation norm1 ->
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
                          | uu____19208 ->
                              let uu____19209 =
                                let uu____19210 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19211 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19210
                                  uu____19211 in
                              failwith uu____19209)
                     | uu____19236 ->
                         let uu____19237 =
                           let uu____19238 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19238.FStar_Syntax_Syntax.n in
                         (match uu____19237 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19283 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19283 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19315 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19315 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19398 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19454 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19454
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19466 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19560  ->
                            fun lb  ->
                              match uu____19560 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19655 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19655
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19658 =
                                      let uu____19673 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19673
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19658 with
                                    | (tok,decl,env2) ->
                                        let uu____19719 =
                                          let uu____19732 =
                                            let uu____19743 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19743, tok) in
                                          uu____19732 :: toks in
                                        (uu____19719, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19466 with
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
                        | uu____19926 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19934 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19934 vars)
                            else
                              (let uu____19936 =
                                 let uu____19943 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19943) in
                               FStar_SMTEncoding_Util.mkApp uu____19936) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20025;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20027;
                             FStar_Syntax_Syntax.lbeff = uu____20028;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20091 =
                              let uu____20098 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20098 with
                              | (tcenv',uu____20116,e_t) ->
                                  let uu____20122 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20133 -> failwith "Impossible" in
                                  (match uu____20122 with
                                   | (e1,t_norm1) ->
                                       ((let uu___170_20149 = env2 in
                                         {
                                           bindings =
                                             (uu___170_20149.bindings);
                                           depth = (uu___170_20149.depth);
                                           tcenv = tcenv';
                                           warn = (uu___170_20149.warn);
                                           cache = (uu___170_20149.cache);
                                           nolabels =
                                             (uu___170_20149.nolabels);
                                           use_zfuel_name =
                                             (uu___170_20149.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___170_20149.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___170_20149.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20091 with
                             | (env',e1,t_norm1) ->
                                 let uu____20159 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20159 with
                                  | ((binders,body,uu____20180,uu____20181),curry)
                                      ->
                                      ((let uu____20192 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20192
                                        then
                                          let uu____20193 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20194 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20193 uu____20194
                                        else ());
                                       (let uu____20196 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20196 with
                                        | (vars,guards,env'1,binder_decls,uu____20223)
                                            ->
                                            let body1 =
                                              let uu____20237 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20237
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20240 =
                                              let uu____20249 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20249
                                              then
                                                let uu____20260 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20261 =
                                                  encode_formula body1 env'1 in
                                                (uu____20260, uu____20261)
                                              else
                                                (let uu____20271 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20271)) in
                                            (match uu____20240 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20294 =
                                                     let uu____20301 =
                                                       let uu____20302 =
                                                         let uu____20313 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20313) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20302 in
                                                     let uu____20324 =
                                                       let uu____20327 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20327 in
                                                     (uu____20301,
                                                       uu____20324,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20294 in
                                                 let uu____20330 =
                                                   let uu____20333 =
                                                     let uu____20336 =
                                                       let uu____20339 =
                                                         let uu____20342 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20342 in
                                                       FStar_List.append
                                                         decls2 uu____20339 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20336 in
                                                   FStar_List.append decls1
                                                     uu____20333 in
                                                 (uu____20330, env2))))))
                        | uu____20347 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20432 = varops.fresh "fuel" in
                          (uu____20432, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20435 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20523  ->
                                  fun uu____20524  ->
                                    match (uu____20523, uu____20524) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20672 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20672 in
                                        let gtok =
                                          let uu____20674 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20674 in
                                        let env4 =
                                          let uu____20676 =
                                            let uu____20679 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20679 in
                                          push_free_var env3 flid gtok
                                            uu____20676 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20435 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20835 t_norm
                              uu____20837 =
                              match (uu____20835, uu____20837) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20881;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20882;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20910 =
                                    let uu____20917 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20917 with
                                    | (tcenv',uu____20939,e_t) ->
                                        let uu____20945 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20956 ->
                                              failwith "Impossible" in
                                        (match uu____20945 with
                                         | (e1,t_norm1) ->
                                             ((let uu___171_20972 = env3 in
                                               {
                                                 bindings =
                                                   (uu___171_20972.bindings);
                                                 depth =
                                                   (uu___171_20972.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___171_20972.warn);
                                                 cache =
                                                   (uu___171_20972.cache);
                                                 nolabels =
                                                   (uu___171_20972.nolabels);
                                                 use_zfuel_name =
                                                   (uu___171_20972.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___171_20972.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___171_20972.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20910 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20987 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20987
                                         then
                                           let uu____20988 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20989 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20990 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20988 uu____20989
                                             uu____20990
                                         else ());
                                        (let uu____20992 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20992 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21029 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21029
                                               then
                                                 let uu____21030 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21031 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21032 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21033 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21030 uu____21031
                                                   uu____21032 uu____21033
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21037 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21037 with
                                               | (vars,guards,env'1,binder_decls,uu____21068)
                                                   ->
                                                   let decl_g =
                                                     let uu____21082 =
                                                       let uu____21093 =
                                                         let uu____21096 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21096 in
                                                       (g, uu____21093,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21082 in
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
                                                     let uu____21121 =
                                                       let uu____21128 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21128) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21121 in
                                                   let gsapp =
                                                     let uu____21138 =
                                                       let uu____21145 =
                                                         let uu____21148 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21148 ::
                                                           vars_tm in
                                                       (g, uu____21145) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21138 in
                                                   let gmax =
                                                     let uu____21154 =
                                                       let uu____21161 =
                                                         let uu____21164 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21164 ::
                                                           vars_tm in
                                                       (g, uu____21161) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21154 in
                                                   let body1 =
                                                     let uu____21170 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21170
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21172 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21172 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21190 =
                                                            let uu____21197 =
                                                              let uu____21198
                                                                =
                                                                let uu____21213
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
                                                                  uu____21213) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21198 in
                                                            let uu____21234 =
                                                              let uu____21237
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21237 in
                                                            (uu____21197,
                                                              uu____21234,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21190 in
                                                        let eqn_f =
                                                          let uu____21241 =
                                                            let uu____21248 =
                                                              let uu____21249
                                                                =
                                                                let uu____21260
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21260) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21249 in
                                                            (uu____21248,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21241 in
                                                        let eqn_g' =
                                                          let uu____21274 =
                                                            let uu____21281 =
                                                              let uu____21282
                                                                =
                                                                let uu____21293
                                                                  =
                                                                  let uu____21294
                                                                    =
                                                                    let uu____21299
                                                                    =
                                                                    let uu____21300
                                                                    =
                                                                    let uu____21307
                                                                    =
                                                                    let uu____21310
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21310
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21307) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21300 in
                                                                    (gsapp,
                                                                    uu____21299) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21294 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21293) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21282 in
                                                            (uu____21281,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21274 in
                                                        let uu____21333 =
                                                          let uu____21342 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21342
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21371)
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
                                                                  let uu____21396
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21396
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21401
                                                                  =
                                                                  let uu____21408
                                                                    =
                                                                    let uu____21409
                                                                    =
                                                                    let uu____21420
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21420) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21409 in
                                                                  (uu____21408,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21401 in
                                                              let uu____21441
                                                                =
                                                                let uu____21448
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21448
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21461
                                                                    =
                                                                    let uu____21464
                                                                    =
                                                                    let uu____21465
                                                                    =
                                                                    let uu____21472
                                                                    =
                                                                    let uu____21473
                                                                    =
                                                                    let uu____21484
                                                                    =
                                                                    let uu____21485
                                                                    =
                                                                    let uu____21490
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21490,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21485 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21484) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21473 in
                                                                    (uu____21472,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21465 in
                                                                    [uu____21464] in
                                                                    (d3,
                                                                    uu____21461) in
                                                              (match uu____21441
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21333
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
                            let uu____21555 =
                              let uu____21568 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21647  ->
                                   fun uu____21648  ->
                                     match (uu____21647, uu____21648) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21803 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21803 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21568 in
                            (match uu____21555 with
                             | (decls2,eqns,env01) ->
                                 let uu____21876 =
                                   let isDeclFun uu___137_21888 =
                                     match uu___137_21888 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21889 -> true
                                     | uu____21900 -> false in
                                   let uu____21901 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21901
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21876 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21941 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___138_21945  ->
                                 match uu___138_21945 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21946 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21952 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21952))) in
                      if uu____21941
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
                   let uu____22004 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22004
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
        let uu____22053 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22053 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22057 = encode_sigelt' env se in
      match uu____22057 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22073 =
                  let uu____22074 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22074 in
                [uu____22073]
            | uu____22075 ->
                let uu____22076 =
                  let uu____22079 =
                    let uu____22080 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22080 in
                  uu____22079 :: g in
                let uu____22081 =
                  let uu____22084 =
                    let uu____22085 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22085 in
                  [uu____22084] in
                FStar_List.append uu____22076 uu____22081 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22098 =
          let uu____22099 = FStar_Syntax_Subst.compress t in
          uu____22099.FStar_Syntax_Syntax.n in
        match uu____22098 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22103)) -> s = "opaque_to_smt"
        | uu____22104 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22109 =
          let uu____22110 = FStar_Syntax_Subst.compress t in
          uu____22110.FStar_Syntax_Syntax.n in
        match uu____22109 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22114)) -> s = "uninterpreted_by_smt"
        | uu____22115 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22120 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22125 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22128 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22131 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22146 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22150 =
            let uu____22151 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22151 Prims.op_Negation in
          if uu____22150
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22177 ->
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
               let uu____22197 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22197 with
               | (aname,atok,env2) ->
                   let uu____22213 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22213 with
                    | (formals,uu____22231) ->
                        let uu____22244 =
                          let uu____22249 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22249 env2 in
                        (match uu____22244 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22261 =
                                 let uu____22262 =
                                   let uu____22273 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22289  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22273,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22262 in
                               [uu____22261;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22302 =
                               let aux uu____22354 uu____22355 =
                                 match (uu____22354, uu____22355) with
                                 | ((bv,uu____22407),(env3,acc_sorts,acc)) ->
                                     let uu____22445 = gen_term_var env3 bv in
                                     (match uu____22445 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22302 with
                              | (uu____22517,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22540 =
                                      let uu____22547 =
                                        let uu____22548 =
                                          let uu____22559 =
                                            let uu____22560 =
                                              let uu____22565 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22565) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22560 in
                                          ([[app]], xs_sorts, uu____22559) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22548 in
                                      (uu____22547,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22540 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22585 =
                                      let uu____22592 =
                                        let uu____22593 =
                                          let uu____22604 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22604) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22593 in
                                      (uu____22592,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22585 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22623 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22623 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22651,uu____22652)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22653 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22653 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22670,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22676 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___139_22680  ->
                      match uu___139_22680 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22681 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22686 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22687 -> false)) in
            Prims.op_Negation uu____22676 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22696 =
               let uu____22703 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22703 env fv t quals in
             match uu____22696 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22718 =
                   let uu____22721 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22721 in
                 (uu____22718, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22729 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22729 with
           | (uu____22738,f1) ->
               let uu____22740 = encode_formula f1 env in
               (match uu____22740 with
                | (f2,decls) ->
                    let g =
                      let uu____22754 =
                        let uu____22755 =
                          let uu____22762 =
                            let uu____22765 =
                              let uu____22766 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22766 in
                            FStar_Pervasives_Native.Some uu____22765 in
                          let uu____22767 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22762, uu____22767) in
                        FStar_SMTEncoding_Util.mkAssume uu____22755 in
                      [uu____22754] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22773) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22785 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22803 =
                       let uu____22806 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22806.FStar_Syntax_Syntax.fv_name in
                     uu____22803.FStar_Syntax_Syntax.v in
                   let uu____22807 =
                     let uu____22808 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22808 in
                   if uu____22807
                   then
                     let val_decl =
                       let uu___174_22836 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___174_22836.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___174_22836.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___174_22836.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22841 = encode_sigelt' env1 val_decl in
                     match uu____22841 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22785 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22869,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22871;
                          FStar_Syntax_Syntax.lbtyp = uu____22872;
                          FStar_Syntax_Syntax.lbeff = uu____22873;
                          FStar_Syntax_Syntax.lbdef = uu____22874;_}::[]),uu____22875)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22894 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22894 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22923 =
                   let uu____22926 =
                     let uu____22927 =
                       let uu____22934 =
                         let uu____22935 =
                           let uu____22946 =
                             let uu____22947 =
                               let uu____22952 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22952) in
                             FStar_SMTEncoding_Util.mkEq uu____22947 in
                           ([[b2t_x]], [xx], uu____22946) in
                         FStar_SMTEncoding_Util.mkForall uu____22935 in
                       (uu____22934,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22927 in
                   [uu____22926] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22923 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22985,uu____22986) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___140_22995  ->
                  match uu___140_22995 with
                  | FStar_Syntax_Syntax.Discriminator uu____22996 -> true
                  | uu____22997 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23000,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23011 =
                     let uu____23012 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23012.FStar_Ident.idText in
                   uu____23011 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___141_23016  ->
                     match uu___141_23016 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23017 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23021) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___142_23038  ->
                  match uu___142_23038 with
                  | FStar_Syntax_Syntax.Projector uu____23039 -> true
                  | uu____23044 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23047 = try_lookup_free_var env l in
          (match uu____23047 with
           | FStar_Pervasives_Native.Some uu____23054 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___175_23058 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___175_23058.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___175_23058.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___175_23058.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23065) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23083) ->
          let uu____23092 = encode_sigelts env ses in
          (match uu____23092 with
           | (g,env1) ->
               let uu____23109 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___143_23132  ->
                         match uu___143_23132 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23133;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23134;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23135;_}
                             -> false
                         | uu____23138 -> true)) in
               (match uu____23109 with
                | (g',inversions) ->
                    let uu____23153 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___144_23174  ->
                              match uu___144_23174 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23175 ->
                                  true
                              | uu____23186 -> false)) in
                    (match uu____23153 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23204,tps,k,uu____23207,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___145_23224  ->
                    match uu___145_23224 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23225 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23234 = c in
              match uu____23234 with
              | (name,args,uu____23239,uu____23240,uu____23241) ->
                  let uu____23246 =
                    let uu____23247 =
                      let uu____23258 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23275  ->
                                match uu____23275 with
                                | (uu____23282,sort,uu____23284) -> sort)) in
                      (name, uu____23258, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23247 in
                  [uu____23246]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23311 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23317 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23317 FStar_Option.isNone)) in
            if uu____23311
            then []
            else
              (let uu____23349 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23349 with
               | (xxsym,xx) ->
                   let uu____23358 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23397  ->
                             fun l  ->
                               match uu____23397 with
                               | (out,decls) ->
                                   let uu____23417 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23417 with
                                    | (uu____23428,data_t) ->
                                        let uu____23430 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23430 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23476 =
                                                 let uu____23477 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23477.FStar_Syntax_Syntax.n in
                                               match uu____23476 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23488,indices) ->
                                                   indices
                                               | uu____23510 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23534  ->
                                                         match uu____23534
                                                         with
                                                         | (x,uu____23540) ->
                                                             let uu____23541
                                                               =
                                                               let uu____23542
                                                                 =
                                                                 let uu____23549
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23549,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23542 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23541)
                                                    env) in
                                             let uu____23552 =
                                               encode_args indices env1 in
                                             (match uu____23552 with
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
                                                      let uu____23578 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23594
                                                                 =
                                                                 let uu____23599
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23599,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23594)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23578
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23602 =
                                                      let uu____23603 =
                                                        let uu____23608 =
                                                          let uu____23609 =
                                                            let uu____23614 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23614,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23609 in
                                                        (out, uu____23608) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23603 in
                                                    (uu____23602,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23358 with
                    | (data_ax,decls) ->
                        let uu____23627 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23627 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23638 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23638 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23642 =
                                 let uu____23649 =
                                   let uu____23650 =
                                     let uu____23661 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23676 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23661,
                                       uu____23676) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23650 in
                                 let uu____23691 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23649,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23691) in
                               FStar_SMTEncoding_Util.mkAssume uu____23642 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23694 =
            let uu____23707 =
              let uu____23708 = FStar_Syntax_Subst.compress k in
              uu____23708.FStar_Syntax_Syntax.n in
            match uu____23707 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23753 -> (tps, k) in
          (match uu____23694 with
           | (formals,res) ->
               let uu____23776 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23776 with
                | (formals1,res1) ->
                    let uu____23787 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23787 with
                     | (vars,guards,env',binder_decls,uu____23812) ->
                         let uu____23825 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23825 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23844 =
                                  let uu____23851 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23851) in
                                FStar_SMTEncoding_Util.mkApp uu____23844 in
                              let uu____23860 =
                                let tname_decl =
                                  let uu____23870 =
                                    let uu____23871 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23903  ->
                                              match uu____23903 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23916 = varops.next_id () in
                                    (tname, uu____23871,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23916, false) in
                                  constructor_or_logic_type_decl uu____23870 in
                                let uu____23925 =
                                  match vars with
                                  | [] ->
                                      let uu____23938 =
                                        let uu____23939 =
                                          let uu____23942 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23942 in
                                        push_free_var env1 t tname
                                          uu____23939 in
                                      ([], uu____23938)
                                  | uu____23949 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23958 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23958 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23972 =
                                          let uu____23979 =
                                            let uu____23980 =
                                              let uu____23995 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23995) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23980 in
                                          (uu____23979,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23972 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23925 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23860 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24035 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24035 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24053 =
                                               let uu____24054 =
                                                 let uu____24061 =
                                                   let uu____24062 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24062 in
                                                 (uu____24061,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24054 in
                                             [uu____24053]
                                           else [] in
                                         let uu____24066 =
                                           let uu____24069 =
                                             let uu____24072 =
                                               let uu____24073 =
                                                 let uu____24080 =
                                                   let uu____24081 =
                                                     let uu____24092 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24092) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24081 in
                                                 (uu____24080,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24073 in
                                             [uu____24072] in
                                           FStar_List.append karr uu____24069 in
                                         FStar_List.append decls1 uu____24066 in
                                   let aux =
                                     let uu____24108 =
                                       let uu____24111 =
                                         inversion_axioms tapp vars in
                                       let uu____24114 =
                                         let uu____24117 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24117] in
                                       FStar_List.append uu____24111
                                         uu____24114 in
                                     FStar_List.append kindingAx uu____24108 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24124,uu____24125,uu____24126,uu____24127,uu____24128)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24136,t,uu____24138,n_tps,uu____24140) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24148 = new_term_constant_and_tok_from_lid env d in
          (match uu____24148 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24165 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24165 with
                | (formals,t_res) ->
                    let uu____24200 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24200 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24214 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24214 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24284 =
                                            mk_term_projector_name d x in
                                          (uu____24284,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24286 =
                                  let uu____24305 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24305, true) in
                                FStar_All.pipe_right uu____24286
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
                              let uu____24344 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24344 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24356::uu____24357 ->
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
                                         let uu____24402 =
                                           let uu____24413 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24413) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24402
                                     | uu____24438 -> tok_typing in
                                   let uu____24447 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24447 with
                                    | (vars',guards',env'',decls_formals,uu____24472)
                                        ->
                                        let uu____24485 =
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
                                        (match uu____24485 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24516 ->
                                                   let uu____24523 =
                                                     let uu____24524 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24524 in
                                                   [uu____24523] in
                                             let encode_elim uu____24534 =
                                               let uu____24535 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24535 with
                                               | (head1,args) ->
                                                   let uu____24578 =
                                                     let uu____24579 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24579.FStar_Syntax_Syntax.n in
                                                   (match uu____24578 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24589;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24590;_},uu____24591)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24597 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24597
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
                                                                 | uu____24640
                                                                    ->
                                                                    let uu____24641
                                                                    =
                                                                    let uu____24642
                                                                    =
                                                                    let uu____24647
                                                                    =
                                                                    let uu____24648
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24648 in
                                                                    (uu____24647,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24642 in
                                                                    FStar_Exn.raise
                                                                    uu____24641 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24664
                                                                    =
                                                                    let uu____24665
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24665 in
                                                                    if
                                                                    uu____24664
                                                                    then
                                                                    let uu____24678
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24678]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24680
                                                               =
                                                               let uu____24693
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24743
                                                                     ->
                                                                    fun
                                                                    uu____24744
                                                                     ->
                                                                    match 
                                                                    (uu____24743,
                                                                    uu____24744)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24839
                                                                    =
                                                                    let uu____24846
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24846 in
                                                                    (match uu____24839
                                                                    with
                                                                    | 
                                                                    (uu____24859,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24867
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24867
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24869
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24869
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
                                                                 uu____24693 in
                                                             (match uu____24680
                                                              with
                                                              | (uu____24884,arg_vars,elim_eqns_or_guards,uu____24887)
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
                                                                    let uu____24917
                                                                    =
                                                                    let uu____24924
                                                                    =
                                                                    let uu____24925
                                                                    =
                                                                    let uu____24936
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24947
                                                                    =
                                                                    let uu____24948
                                                                    =
                                                                    let uu____24953
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24953) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24948 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24936,
                                                                    uu____24947) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24925 in
                                                                    (uu____24924,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24917 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24976
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24976,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24978
                                                                    =
                                                                    let uu____24985
                                                                    =
                                                                    let uu____24986
                                                                    =
                                                                    let uu____24997
                                                                    =
                                                                    let uu____25002
                                                                    =
                                                                    let uu____25005
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25005] in
                                                                    [uu____25002] in
                                                                    let uu____25010
                                                                    =
                                                                    let uu____25011
                                                                    =
                                                                    let uu____25016
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25017
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25016,
                                                                    uu____25017) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25011 in
                                                                    (uu____24997,
                                                                    [x],
                                                                    uu____25010) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24986 in
                                                                    let uu____25036
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24985,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25036) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24978
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25043
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
                                                                    (let uu____25071
                                                                    =
                                                                    let uu____25072
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25072
                                                                    dapp1 in
                                                                    [uu____25071]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25043
                                                                    FStar_List.flatten in
                                                                    let uu____25079
                                                                    =
                                                                    let uu____25086
                                                                    =
                                                                    let uu____25087
                                                                    =
                                                                    let uu____25098
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25109
                                                                    =
                                                                    let uu____25110
                                                                    =
                                                                    let uu____25115
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25115) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25110 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25098,
                                                                    uu____25109) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25087 in
                                                                    (uu____25086,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25079) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25136 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25136
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
                                                                 | uu____25179
                                                                    ->
                                                                    let uu____25180
                                                                    =
                                                                    let uu____25181
                                                                    =
                                                                    let uu____25186
                                                                    =
                                                                    let uu____25187
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25187 in
                                                                    (uu____25186,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25181 in
                                                                    FStar_Exn.raise
                                                                    uu____25180 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25203
                                                                    =
                                                                    let uu____25204
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25204 in
                                                                    if
                                                                    uu____25203
                                                                    then
                                                                    let uu____25217
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25217]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25219
                                                               =
                                                               let uu____25232
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25282
                                                                     ->
                                                                    fun
                                                                    uu____25283
                                                                     ->
                                                                    match 
                                                                    (uu____25282,
                                                                    uu____25283)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25378
                                                                    =
                                                                    let uu____25385
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25385 in
                                                                    (match uu____25378
                                                                    with
                                                                    | 
                                                                    (uu____25398,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25406
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25406
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25408
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25408
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
                                                                 uu____25232 in
                                                             (match uu____25219
                                                              with
                                                              | (uu____25423,arg_vars,elim_eqns_or_guards,uu____25426)
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
                                                                    let uu____25456
                                                                    =
                                                                    let uu____25463
                                                                    =
                                                                    let uu____25464
                                                                    =
                                                                    let uu____25475
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25486
                                                                    =
                                                                    let uu____25487
                                                                    =
                                                                    let uu____25492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25492) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25487 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25475,
                                                                    uu____25486) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25464 in
                                                                    (uu____25463,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25456 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25515
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25515,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25517
                                                                    =
                                                                    let uu____25524
                                                                    =
                                                                    let uu____25525
                                                                    =
                                                                    let uu____25536
                                                                    =
                                                                    let uu____25541
                                                                    =
                                                                    let uu____25544
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25544] in
                                                                    [uu____25541] in
                                                                    let uu____25549
                                                                    =
                                                                    let uu____25550
                                                                    =
                                                                    let uu____25555
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25556
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25555,
                                                                    uu____25556) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25550 in
                                                                    (uu____25536,
                                                                    [x],
                                                                    uu____25549) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25525 in
                                                                    let uu____25575
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25524,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25575) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25517
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25582
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
                                                                    (let uu____25610
                                                                    =
                                                                    let uu____25611
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25611
                                                                    dapp1 in
                                                                    [uu____25610]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25582
                                                                    FStar_List.flatten in
                                                                    let uu____25618
                                                                    =
                                                                    let uu____25625
                                                                    =
                                                                    let uu____25626
                                                                    =
                                                                    let uu____25637
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25648
                                                                    =
                                                                    let uu____25649
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25654) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25649 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25637,
                                                                    uu____25648) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25626 in
                                                                    (uu____25625,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25618) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25673 ->
                                                        ((let uu____25675 =
                                                            let uu____25676 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25677 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25676
                                                              uu____25677 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25675);
                                                         ([], []))) in
                                             let uu____25682 = encode_elim () in
                                             (match uu____25682 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25702 =
                                                      let uu____25705 =
                                                        let uu____25708 =
                                                          let uu____25711 =
                                                            let uu____25714 =
                                                              let uu____25715
                                                                =
                                                                let uu____25726
                                                                  =
                                                                  let uu____25729
                                                                    =
                                                                    let uu____25730
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25730 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25729 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25726) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25715 in
                                                            [uu____25714] in
                                                          let uu____25735 =
                                                            let uu____25738 =
                                                              let uu____25741
                                                                =
                                                                let uu____25744
                                                                  =
                                                                  let uu____25747
                                                                    =
                                                                    let uu____25750
                                                                    =
                                                                    let uu____25753
                                                                    =
                                                                    let uu____25754
                                                                    =
                                                                    let uu____25761
                                                                    =
                                                                    let uu____25762
                                                                    =
                                                                    let uu____25773
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25773) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25762 in
                                                                    (uu____25761,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25754 in
                                                                    let uu____25786
                                                                    =
                                                                    let uu____25789
                                                                    =
                                                                    let uu____25790
                                                                    =
                                                                    let uu____25797
                                                                    =
                                                                    let uu____25798
                                                                    =
                                                                    let uu____25809
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25820
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25809,
                                                                    uu____25820) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25798 in
                                                                    (uu____25797,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25790 in
                                                                    [uu____25789] in
                                                                    uu____25753
                                                                    ::
                                                                    uu____25786 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25750 in
                                                                  FStar_List.append
                                                                    uu____25747
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25744 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25741 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25738 in
                                                          FStar_List.append
                                                            uu____25711
                                                            uu____25735 in
                                                        FStar_List.append
                                                          decls3 uu____25708 in
                                                      FStar_List.append
                                                        decls2 uu____25705 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25702 in
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
           (fun uu____25866  ->
              fun se  ->
                match uu____25866 with
                | (g,env1) ->
                    let uu____25886 = encode_sigelt env1 se in
                    (match uu____25886 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25945 =
        match uu____25945 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25977 ->
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
                 ((let uu____25983 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25983
                   then
                     let uu____25984 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25985 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25986 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25984 uu____25985 uu____25986
                   else ());
                  (let uu____25988 = encode_term t1 env1 in
                   match uu____25988 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26004 =
                         let uu____26011 =
                           let uu____26012 =
                             let uu____26013 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26013
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26012 in
                         new_term_constant_from_string env1 x uu____26011 in
                       (match uu____26004 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26029 = FStar_Options.log_queries () in
                              if uu____26029
                              then
                                let uu____26032 =
                                  let uu____26033 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26034 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26035 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26033 uu____26034 uu____26035 in
                                FStar_Pervasives_Native.Some uu____26032
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26051,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26065 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26065 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26088,se,uu____26090) ->
                 let uu____26095 = encode_sigelt env1 se in
                 (match uu____26095 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26112,se) ->
                 let uu____26118 = encode_sigelt env1 se in
                 (match uu____26118 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26135 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26135 with | (uu____26158,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26173 'Auu____26174 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26174,'Auu____26173)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26242  ->
              match uu____26242 with
              | (l,uu____26254,uu____26255) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26301  ->
              match uu____26301 with
              | (l,uu____26315,uu____26316) ->
                  let uu____26325 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26326 =
                    let uu____26329 =
                      let uu____26330 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26330 in
                    [uu____26329] in
                  uu____26325 :: uu____26326)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26352 =
      let uu____26355 =
        let uu____26356 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26359 =
          let uu____26360 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26360 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26356;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26359
        } in
      [uu____26355] in
    FStar_ST.op_Colon_Equals last_env uu____26352
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26419 = FStar_ST.op_Bang last_env in
      match uu____26419 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26473 ->
          let uu___176_26476 = e in
          let uu____26477 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___176_26476.bindings);
            depth = (uu___176_26476.depth);
            tcenv;
            warn = (uu___176_26476.warn);
            cache = (uu___176_26476.cache);
            nolabels = (uu___176_26476.nolabels);
            use_zfuel_name = (uu___176_26476.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___176_26476.encode_non_total_function_typ);
            current_module_name = uu____26477
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26482 = FStar_ST.op_Bang last_env in
    match uu____26482 with
    | [] -> failwith "Empty env stack"
    | uu____26535::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26592  ->
    let uu____26593 = FStar_ST.op_Bang last_env in
    match uu____26593 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___177_26654 = hd1 in
          {
            bindings = (uu___177_26654.bindings);
            depth = (uu___177_26654.depth);
            tcenv = (uu___177_26654.tcenv);
            warn = (uu___177_26654.warn);
            cache = refs;
            nolabels = (uu___177_26654.nolabels);
            use_zfuel_name = (uu___177_26654.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26654.encode_non_total_function_typ);
            current_module_name = (uu___177_26654.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26708  ->
    let uu____26709 = FStar_ST.op_Bang last_env in
    match uu____26709 with
    | [] -> failwith "Popping an empty stack"
    | uu____26762::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26860::uu____26861,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___178_26869 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___178_26869.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___178_26869.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___178_26869.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26870 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26887 =
        let uu____26890 =
          let uu____26891 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26891 in
        let uu____26892 = open_fact_db_tags env in uu____26890 :: uu____26892 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26887
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
      let uu____26916 = encode_sigelt env se in
      match uu____26916 with
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
        let uu____26954 = FStar_Options.log_queries () in
        if uu____26954
        then
          let uu____26957 =
            let uu____26958 =
              let uu____26959 =
                let uu____26960 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26960 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26959 in
            FStar_SMTEncoding_Term.Caption uu____26958 in
          uu____26957 :: decls
        else decls in
      (let uu____26971 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26971
       then
         let uu____26972 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26972
       else ());
      (let env =
         let uu____26975 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26975 tcenv in
       let uu____26976 = encode_top_level_facts env se in
       match uu____26976 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26990 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26990)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27004 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27004
       then
         let uu____27005 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27005
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27040  ->
                 fun se  ->
                   match uu____27040 with
                   | (g,env2) ->
                       let uu____27060 = encode_top_level_facts env2 se in
                       (match uu____27060 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27083 =
         encode_signature
           (let uu___179_27092 = env in
            {
              bindings = (uu___179_27092.bindings);
              depth = (uu___179_27092.depth);
              tcenv = (uu___179_27092.tcenv);
              warn = false;
              cache = (uu___179_27092.cache);
              nolabels = (uu___179_27092.nolabels);
              use_zfuel_name = (uu___179_27092.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___179_27092.encode_non_total_function_typ);
              current_module_name = (uu___179_27092.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27083 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27109 = FStar_Options.log_queries () in
             if uu____27109
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___180_27117 = env1 in
               {
                 bindings = (uu___180_27117.bindings);
                 depth = (uu___180_27117.depth);
                 tcenv = (uu___180_27117.tcenv);
                 warn = true;
                 cache = (uu___180_27117.cache);
                 nolabels = (uu___180_27117.nolabels);
                 use_zfuel_name = (uu___180_27117.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___180_27117.encode_non_total_function_typ);
                 current_module_name = (uu___180_27117.current_module_name)
               });
            (let uu____27119 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27119
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
        (let uu____27174 =
           let uu____27175 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27175.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27174);
        (let env =
           let uu____27177 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27177 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27189 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27224 = aux rest in
                 (match uu____27224 with
                  | (out,rest1) ->
                      let t =
                        let uu____27254 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27254 with
                        | FStar_Pervasives_Native.Some uu____27259 ->
                            let uu____27260 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27260
                              x.FStar_Syntax_Syntax.sort
                        | uu____27261 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27265 =
                        let uu____27268 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___181_27271 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___181_27271.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___181_27271.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27268 :: out in
                      (uu____27265, rest1))
             | uu____27276 -> ([], bindings1) in
           let uu____27283 = aux bindings in
           match uu____27283 with
           | (closing,bindings1) ->
               let uu____27308 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27308, bindings1) in
         match uu____27189 with
         | (q1,bindings1) ->
             let uu____27331 =
               let uu____27336 =
                 FStar_List.filter
                   (fun uu___146_27341  ->
                      match uu___146_27341 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27342 ->
                          false
                      | uu____27349 -> true) bindings1 in
               encode_env_bindings env uu____27336 in
             (match uu____27331 with
              | (env_decls,env1) ->
                  ((let uu____27367 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27367
                    then
                      let uu____27368 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27368
                    else ());
                   (let uu____27370 = encode_formula q1 env1 in
                    match uu____27370 with
                    | (phi,qdecls) ->
                        let uu____27391 =
                          let uu____27396 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27396 phi in
                        (match uu____27391 with
                         | (labels,phi1) ->
                             let uu____27413 = encode_labels labels in
                             (match uu____27413 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27450 =
                                      let uu____27457 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27458 =
                                        varops.mk_unique "@query" in
                                      (uu____27457,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27458) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27450 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))