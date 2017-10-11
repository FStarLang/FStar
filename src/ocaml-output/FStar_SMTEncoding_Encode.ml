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
                                     [FStar_TypeChecker_Normalize.WHNF;
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
            let uu___157_10409 = env in
            {
              bindings = (uu___157_10409.bindings);
              depth = (uu___157_10409.depth);
              tcenv = (uu___157_10409.tcenv);
              warn = (uu___157_10409.warn);
              cache = (uu___157_10409.cache);
              nolabels = (uu___157_10409.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___157_10409.encode_non_total_function_typ);
              current_module_name = (uu___157_10409.current_module_name)
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
                    let env3 =
                      let uu___158_10623 = env2 in
                      {
                        bindings = (uu___158_10623.bindings);
                        depth = (uu___158_10623.depth);
                        tcenv = (uu___158_10623.tcenv);
                        warn = (uu___158_10623.warn);
                        cache = (uu___158_10623.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___158_10623.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___158_10623.encode_non_total_function_typ);
                        current_module_name =
                          (uu___158_10623.current_module_name)
                      } in
                    let uu____10624 =
                      let uu____10629 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10629 env3 in
                    (match uu____10624 with
                     | (pre1,decls'') ->
                         let uu____10636 =
                           let uu____10641 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10641 env3 in
                         (match uu____10636 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10651 =
                                let uu____10652 =
                                  let uu____10663 =
                                    let uu____10664 =
                                      let uu____10669 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10669, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10664 in
                                  (pats, vars, uu____10663) in
                                FStar_SMTEncoding_Util.mkForall uu____10652 in
                              (uu____10651, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10688 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10688
        then
          let uu____10689 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10690 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10689 uu____10690
        else () in
      let enc f r l =
        let uu____10723 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10751 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10751 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10723 with
        | (decls,args) ->
            let uu____10780 =
              let uu___159_10781 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___159_10781.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___159_10781.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10780, decls) in
      let const_op f r uu____10812 =
        let uu____10825 = f r in (uu____10825, []) in
      let un_op f l =
        let uu____10844 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10844 in
      let bin_op f uu___133_10860 =
        match uu___133_10860 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10871 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10905 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10928  ->
                 match uu____10928 with
                 | (t,uu____10942) ->
                     let uu____10943 = encode_formula t env in
                     (match uu____10943 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10905 with
        | (decls,phis) ->
            let uu____10972 =
              let uu___160_10973 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_10973.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_10973.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10972, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11034  ->
               match uu____11034 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11053) -> false
                    | uu____11054 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11069 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11069
        else
          (let uu____11083 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11083 r rf) in
      let mk_imp1 r uu___134_11108 =
        match uu___134_11108 with
        | (lhs,uu____11114)::(rhs,uu____11116)::[] ->
            let uu____11143 = encode_formula rhs env in
            (match uu____11143 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11158) ->
                      (l1, decls1)
                  | uu____11163 ->
                      let uu____11164 = encode_formula lhs env in
                      (match uu____11164 with
                       | (l2,decls2) ->
                           let uu____11175 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11175, (FStar_List.append decls1 decls2)))))
        | uu____11178 -> failwith "impossible" in
      let mk_ite r uu___135_11199 =
        match uu___135_11199 with
        | (guard,uu____11205)::(_then,uu____11207)::(_else,uu____11209)::[]
            ->
            let uu____11246 = encode_formula guard env in
            (match uu____11246 with
             | (g,decls1) ->
                 let uu____11257 = encode_formula _then env in
                 (match uu____11257 with
                  | (t,decls2) ->
                      let uu____11268 = encode_formula _else env in
                      (match uu____11268 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11282 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11307 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11307 in
      let connectives =
        let uu____11325 =
          let uu____11338 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11338) in
        let uu____11355 =
          let uu____11370 =
            let uu____11383 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11383) in
          let uu____11400 =
            let uu____11415 =
              let uu____11430 =
                let uu____11443 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11443) in
              let uu____11460 =
                let uu____11475 =
                  let uu____11490 =
                    let uu____11503 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11503) in
                  [uu____11490;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11475 in
              uu____11430 :: uu____11460 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11415 in
          uu____11370 :: uu____11400 in
        uu____11325 :: uu____11355 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11824 = encode_formula phi' env in
            (match uu____11824 with
             | (phi2,decls) ->
                 let uu____11835 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11835, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11836 ->
            let uu____11843 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11843 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11882 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11882 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11894;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11896;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11917 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11917 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11964::(x,uu____11966)::(t,uu____11968)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12015 = encode_term x env in
                 (match uu____12015 with
                  | (x1,decls) ->
                      let uu____12026 = encode_term t env in
                      (match uu____12026 with
                       | (t1,decls') ->
                           let uu____12037 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12037, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12042)::(msg,uu____12044)::(phi2,uu____12046)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12091 =
                   let uu____12096 =
                     let uu____12097 = FStar_Syntax_Subst.compress r in
                     uu____12097.FStar_Syntax_Syntax.n in
                   let uu____12100 =
                     let uu____12101 = FStar_Syntax_Subst.compress msg in
                     uu____12101.FStar_Syntax_Syntax.n in
                   (uu____12096, uu____12100) in
                 (match uu____12091 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12110))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12116 -> fallback phi2)
             | uu____12121 when head_redex env head2 ->
                 let uu____12134 = whnf env phi1 in
                 encode_formula uu____12134 env
             | uu____12135 ->
                 let uu____12148 = encode_term phi1 env in
                 (match uu____12148 with
                  | (tt,decls) ->
                      let uu____12159 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___161_12162 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___161_12162.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___161_12162.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12159, decls)))
        | uu____12163 ->
            let uu____12164 = encode_term phi1 env in
            (match uu____12164 with
             | (tt,decls) ->
                 let uu____12175 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___162_12178 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___162_12178.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___162_12178.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12175, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12214 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12214 with
        | (vars,guards,env2,decls,uu____12253) ->
            let uu____12266 =
              let uu____12279 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12327 =
                          let uu____12336 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12366  ->
                                    match uu____12366 with
                                    | (t,uu____12376) ->
                                        encode_term t
                                          (let uu___163_12378 = env2 in
                                           {
                                             bindings =
                                               (uu___163_12378.bindings);
                                             depth = (uu___163_12378.depth);
                                             tcenv = (uu___163_12378.tcenv);
                                             warn = (uu___163_12378.warn);
                                             cache = (uu___163_12378.cache);
                                             nolabels =
                                               (uu___163_12378.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___163_12378.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___163_12378.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12336 FStar_List.unzip in
                        match uu____12327 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12279 FStar_List.unzip in
            (match uu____12266 with
             | (pats,decls') ->
                 let uu____12477 = encode_formula body env2 in
                 (match uu____12477 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12509;
                             FStar_SMTEncoding_Term.rng = uu____12510;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12525 -> guards in
                      let uu____12530 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12530, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12590  ->
                   match uu____12590 with
                   | (x,uu____12596) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12604 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12616 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12616) uu____12604 tl1 in
             let uu____12619 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12646  ->
                       match uu____12646 with
                       | (b,uu____12652) ->
                           let uu____12653 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12653)) in
             (match uu____12619 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12659) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12673 =
                    let uu____12674 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12674 in
                  FStar_Errors.warn pos uu____12673) in
       let uu____12675 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12675 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12684 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12742  ->
                     match uu____12742 with
                     | (l,uu____12756) -> FStar_Ident.lid_equals op l)) in
           (match uu____12684 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12789,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12829 = encode_q_body env vars pats body in
             match uu____12829 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12874 =
                     let uu____12885 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12885) in
                   FStar_SMTEncoding_Term.mkForall uu____12874
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12904 = encode_q_body env vars pats body in
             match uu____12904 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12948 =
                   let uu____12949 =
                     let uu____12960 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12960) in
                   FStar_SMTEncoding_Term.mkExists uu____12949
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12948, decls))))
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
  let uu____13058 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13058 with
  | (asym,a) ->
      let uu____13065 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13065 with
       | (xsym,x) ->
           let uu____13072 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13072 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13116 =
                      let uu____13127 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13127, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13116 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13153 =
                      let uu____13160 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13160) in
                    FStar_SMTEncoding_Util.mkApp uu____13153 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13173 =
                    let uu____13176 =
                      let uu____13179 =
                        let uu____13182 =
                          let uu____13183 =
                            let uu____13190 =
                              let uu____13191 =
                                let uu____13202 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13202) in
                              FStar_SMTEncoding_Util.mkForall uu____13191 in
                            (uu____13190, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13183 in
                        let uu____13219 =
                          let uu____13222 =
                            let uu____13223 =
                              let uu____13230 =
                                let uu____13231 =
                                  let uu____13242 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13242) in
                                FStar_SMTEncoding_Util.mkForall uu____13231 in
                              (uu____13230,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13223 in
                          [uu____13222] in
                        uu____13182 :: uu____13219 in
                      xtok_decl :: uu____13179 in
                    xname_decl :: uu____13176 in
                  (xtok1, uu____13173) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13333 =
                    let uu____13346 =
                      let uu____13355 =
                        let uu____13356 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13356 in
                      quant axy uu____13355 in
                    (FStar_Parser_Const.op_Eq, uu____13346) in
                  let uu____13365 =
                    let uu____13380 =
                      let uu____13393 =
                        let uu____13402 =
                          let uu____13403 =
                            let uu____13404 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13404 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13403 in
                        quant axy uu____13402 in
                      (FStar_Parser_Const.op_notEq, uu____13393) in
                    let uu____13413 =
                      let uu____13428 =
                        let uu____13441 =
                          let uu____13450 =
                            let uu____13451 =
                              let uu____13452 =
                                let uu____13457 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13458 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13457, uu____13458) in
                              FStar_SMTEncoding_Util.mkLT uu____13452 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13451 in
                          quant xy uu____13450 in
                        (FStar_Parser_Const.op_LT, uu____13441) in
                      let uu____13467 =
                        let uu____13482 =
                          let uu____13495 =
                            let uu____13504 =
                              let uu____13505 =
                                let uu____13506 =
                                  let uu____13511 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13512 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13511, uu____13512) in
                                FStar_SMTEncoding_Util.mkLTE uu____13506 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13505 in
                            quant xy uu____13504 in
                          (FStar_Parser_Const.op_LTE, uu____13495) in
                        let uu____13521 =
                          let uu____13536 =
                            let uu____13549 =
                              let uu____13558 =
                                let uu____13559 =
                                  let uu____13560 =
                                    let uu____13565 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13566 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13565, uu____13566) in
                                  FStar_SMTEncoding_Util.mkGT uu____13560 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13559 in
                              quant xy uu____13558 in
                            (FStar_Parser_Const.op_GT, uu____13549) in
                          let uu____13575 =
                            let uu____13590 =
                              let uu____13603 =
                                let uu____13612 =
                                  let uu____13613 =
                                    let uu____13614 =
                                      let uu____13619 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13620 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13619, uu____13620) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13614 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13613 in
                                quant xy uu____13612 in
                              (FStar_Parser_Const.op_GTE, uu____13603) in
                            let uu____13629 =
                              let uu____13644 =
                                let uu____13657 =
                                  let uu____13666 =
                                    let uu____13667 =
                                      let uu____13668 =
                                        let uu____13673 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13674 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13673, uu____13674) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13668 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13667 in
                                  quant xy uu____13666 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13657) in
                              let uu____13683 =
                                let uu____13698 =
                                  let uu____13711 =
                                    let uu____13720 =
                                      let uu____13721 =
                                        let uu____13722 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13722 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13721 in
                                    quant qx uu____13720 in
                                  (FStar_Parser_Const.op_Minus, uu____13711) in
                                let uu____13731 =
                                  let uu____13746 =
                                    let uu____13759 =
                                      let uu____13768 =
                                        let uu____13769 =
                                          let uu____13770 =
                                            let uu____13775 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13776 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13775, uu____13776) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13770 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13769 in
                                      quant xy uu____13768 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13759) in
                                  let uu____13785 =
                                    let uu____13800 =
                                      let uu____13813 =
                                        let uu____13822 =
                                          let uu____13823 =
                                            let uu____13824 =
                                              let uu____13829 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13830 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13829, uu____13830) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13824 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13823 in
                                        quant xy uu____13822 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13813) in
                                    let uu____13839 =
                                      let uu____13854 =
                                        let uu____13867 =
                                          let uu____13876 =
                                            let uu____13877 =
                                              let uu____13878 =
                                                let uu____13883 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13884 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13883, uu____13884) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13878 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13877 in
                                          quant xy uu____13876 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13867) in
                                      let uu____13893 =
                                        let uu____13908 =
                                          let uu____13921 =
                                            let uu____13930 =
                                              let uu____13931 =
                                                let uu____13932 =
                                                  let uu____13937 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13938 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13937, uu____13938) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13932 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13931 in
                                            quant xy uu____13930 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13921) in
                                        let uu____13947 =
                                          let uu____13962 =
                                            let uu____13975 =
                                              let uu____13984 =
                                                let uu____13985 =
                                                  let uu____13986 =
                                                    let uu____13991 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13992 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13991,
                                                      uu____13992) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13986 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13985 in
                                              quant xy uu____13984 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13975) in
                                          let uu____14001 =
                                            let uu____14016 =
                                              let uu____14029 =
                                                let uu____14038 =
                                                  let uu____14039 =
                                                    let uu____14040 =
                                                      let uu____14045 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14046 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14045,
                                                        uu____14046) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14040 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14039 in
                                                quant xy uu____14038 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14029) in
                                            let uu____14055 =
                                              let uu____14070 =
                                                let uu____14083 =
                                                  let uu____14092 =
                                                    let uu____14093 =
                                                      let uu____14094 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14094 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14093 in
                                                  quant qx uu____14092 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14083) in
                                              [uu____14070] in
                                            uu____14016 :: uu____14055 in
                                          uu____13962 :: uu____14001 in
                                        uu____13908 :: uu____13947 in
                                      uu____13854 :: uu____13893 in
                                    uu____13800 :: uu____13839 in
                                  uu____13746 :: uu____13785 in
                                uu____13698 :: uu____13731 in
                              uu____13644 :: uu____13683 in
                            uu____13590 :: uu____13629 in
                          uu____13536 :: uu____13575 in
                        uu____13482 :: uu____13521 in
                      uu____13428 :: uu____13467 in
                    uu____13380 :: uu____13413 in
                  uu____13333 :: uu____13365 in
                let mk1 l v1 =
                  let uu____14308 =
                    let uu____14317 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14375  ->
                              match uu____14375 with
                              | (l',uu____14389) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14317
                      (FStar_Option.map
                         (fun uu____14449  ->
                            match uu____14449 with | (uu____14468,b) -> b v1)) in
                  FStar_All.pipe_right uu____14308 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14539  ->
                          match uu____14539 with
                          | (l',uu____14553) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14594 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14594 with
        | (xxsym,xx) ->
            let uu____14601 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14601 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14611 =
                   let uu____14618 =
                     let uu____14619 =
                       let uu____14630 =
                         let uu____14631 =
                           let uu____14636 =
                             let uu____14637 =
                               let uu____14642 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14642) in
                             FStar_SMTEncoding_Util.mkEq uu____14637 in
                           (xx_has_type, uu____14636) in
                         FStar_SMTEncoding_Util.mkImp uu____14631 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14630) in
                     FStar_SMTEncoding_Util.mkForall uu____14619 in
                   let uu____14667 =
                     let uu____14668 =
                       let uu____14669 =
                         let uu____14670 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14670 in
                       Prims.strcat module_name uu____14669 in
                     varops.mk_unique uu____14668 in
                   (uu____14618, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14667) in
                 FStar_SMTEncoding_Util.mkAssume uu____14611)
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
    let uu____14710 =
      let uu____14711 =
        let uu____14718 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14718, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14711 in
    let uu____14721 =
      let uu____14724 =
        let uu____14725 =
          let uu____14732 =
            let uu____14733 =
              let uu____14744 =
                let uu____14745 =
                  let uu____14750 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14750) in
                FStar_SMTEncoding_Util.mkImp uu____14745 in
              ([[typing_pred]], [xx], uu____14744) in
            mkForall_fuel uu____14733 in
          (uu____14732, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14725 in
      [uu____14724] in
    uu____14710 :: uu____14721 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14792 =
      let uu____14793 =
        let uu____14800 =
          let uu____14801 =
            let uu____14812 =
              let uu____14817 =
                let uu____14820 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14820] in
              [uu____14817] in
            let uu____14825 =
              let uu____14826 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14826 tt in
            (uu____14812, [bb], uu____14825) in
          FStar_SMTEncoding_Util.mkForall uu____14801 in
        (uu____14800, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14793 in
    let uu____14847 =
      let uu____14850 =
        let uu____14851 =
          let uu____14858 =
            let uu____14859 =
              let uu____14870 =
                let uu____14871 =
                  let uu____14876 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14876) in
                FStar_SMTEncoding_Util.mkImp uu____14871 in
              ([[typing_pred]], [xx], uu____14870) in
            mkForall_fuel uu____14859 in
          (uu____14858, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14851 in
      [uu____14850] in
    uu____14792 :: uu____14847 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14926 =
        let uu____14927 =
          let uu____14934 =
            let uu____14937 =
              let uu____14940 =
                let uu____14943 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14944 =
                  let uu____14947 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14947] in
                uu____14943 :: uu____14944 in
              tt :: uu____14940 in
            tt :: uu____14937 in
          ("Prims.Precedes", uu____14934) in
        FStar_SMTEncoding_Util.mkApp uu____14927 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14926 in
    let precedes_y_x =
      let uu____14951 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14951 in
    let uu____14954 =
      let uu____14955 =
        let uu____14962 =
          let uu____14963 =
            let uu____14974 =
              let uu____14979 =
                let uu____14982 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14982] in
              [uu____14979] in
            let uu____14987 =
              let uu____14988 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14988 tt in
            (uu____14974, [bb], uu____14987) in
          FStar_SMTEncoding_Util.mkForall uu____14963 in
        (uu____14962, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14955 in
    let uu____15009 =
      let uu____15012 =
        let uu____15013 =
          let uu____15020 =
            let uu____15021 =
              let uu____15032 =
                let uu____15033 =
                  let uu____15038 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15038) in
                FStar_SMTEncoding_Util.mkImp uu____15033 in
              ([[typing_pred]], [xx], uu____15032) in
            mkForall_fuel uu____15021 in
          (uu____15020, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15013 in
      let uu____15063 =
        let uu____15066 =
          let uu____15067 =
            let uu____15074 =
              let uu____15075 =
                let uu____15086 =
                  let uu____15087 =
                    let uu____15092 =
                      let uu____15093 =
                        let uu____15096 =
                          let uu____15099 =
                            let uu____15102 =
                              let uu____15103 =
                                let uu____15108 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15109 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15108, uu____15109) in
                              FStar_SMTEncoding_Util.mkGT uu____15103 in
                            let uu____15110 =
                              let uu____15113 =
                                let uu____15114 =
                                  let uu____15119 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15120 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15119, uu____15120) in
                                FStar_SMTEncoding_Util.mkGTE uu____15114 in
                              let uu____15121 =
                                let uu____15124 =
                                  let uu____15125 =
                                    let uu____15130 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15131 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15130, uu____15131) in
                                  FStar_SMTEncoding_Util.mkLT uu____15125 in
                                [uu____15124] in
                              uu____15113 :: uu____15121 in
                            uu____15102 :: uu____15110 in
                          typing_pred_y :: uu____15099 in
                        typing_pred :: uu____15096 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15093 in
                    (uu____15092, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15087 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15086) in
              mkForall_fuel uu____15075 in
            (uu____15074,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15067 in
        [uu____15066] in
      uu____15012 :: uu____15063 in
    uu____14954 :: uu____15009 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15177 =
      let uu____15178 =
        let uu____15185 =
          let uu____15186 =
            let uu____15197 =
              let uu____15202 =
                let uu____15205 = FStar_SMTEncoding_Term.boxString b in
                [uu____15205] in
              [uu____15202] in
            let uu____15210 =
              let uu____15211 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15211 tt in
            (uu____15197, [bb], uu____15210) in
          FStar_SMTEncoding_Util.mkForall uu____15186 in
        (uu____15185, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15178 in
    let uu____15232 =
      let uu____15235 =
        let uu____15236 =
          let uu____15243 =
            let uu____15244 =
              let uu____15255 =
                let uu____15256 =
                  let uu____15261 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15261) in
                FStar_SMTEncoding_Util.mkImp uu____15256 in
              ([[typing_pred]], [xx], uu____15255) in
            mkForall_fuel uu____15244 in
          (uu____15243, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15236 in
      [uu____15235] in
    uu____15177 :: uu____15232 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15314 =
      let uu____15315 =
        let uu____15322 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15322, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15315 in
    [uu____15314] in
  let mk_and_interp env conj uu____15334 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15359 =
      let uu____15360 =
        let uu____15367 =
          let uu____15368 =
            let uu____15379 =
              let uu____15380 =
                let uu____15385 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15385, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15380 in
            ([[l_and_a_b]], [aa; bb], uu____15379) in
          FStar_SMTEncoding_Util.mkForall uu____15368 in
        (uu____15367, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15360 in
    [uu____15359] in
  let mk_or_interp env disj uu____15423 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15448 =
      let uu____15449 =
        let uu____15456 =
          let uu____15457 =
            let uu____15468 =
              let uu____15469 =
                let uu____15474 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15474, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15469 in
            ([[l_or_a_b]], [aa; bb], uu____15468) in
          FStar_SMTEncoding_Util.mkForall uu____15457 in
        (uu____15456, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15449 in
    [uu____15448] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15537 =
      let uu____15538 =
        let uu____15545 =
          let uu____15546 =
            let uu____15557 =
              let uu____15558 =
                let uu____15563 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15563, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15558 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15557) in
          FStar_SMTEncoding_Util.mkForall uu____15546 in
        (uu____15545, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15538 in
    [uu____15537] in
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
    let uu____15636 =
      let uu____15637 =
        let uu____15644 =
          let uu____15645 =
            let uu____15656 =
              let uu____15657 =
                let uu____15662 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15662, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15657 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15656) in
          FStar_SMTEncoding_Util.mkForall uu____15645 in
        (uu____15644, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15637 in
    [uu____15636] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15733 =
      let uu____15734 =
        let uu____15741 =
          let uu____15742 =
            let uu____15753 =
              let uu____15754 =
                let uu____15759 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15759, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15754 in
            ([[l_imp_a_b]], [aa; bb], uu____15753) in
          FStar_SMTEncoding_Util.mkForall uu____15742 in
        (uu____15741, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15734 in
    [uu____15733] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15822 =
      let uu____15823 =
        let uu____15830 =
          let uu____15831 =
            let uu____15842 =
              let uu____15843 =
                let uu____15848 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15848, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15843 in
            ([[l_iff_a_b]], [aa; bb], uu____15842) in
          FStar_SMTEncoding_Util.mkForall uu____15831 in
        (uu____15830, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15823 in
    [uu____15822] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15900 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15900 in
    let uu____15903 =
      let uu____15904 =
        let uu____15911 =
          let uu____15912 =
            let uu____15923 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15923) in
          FStar_SMTEncoding_Util.mkForall uu____15912 in
        (uu____15911, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15904 in
    [uu____15903] in
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
      let uu____15983 =
        let uu____15990 =
          let uu____15993 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15993] in
        ("Valid", uu____15990) in
      FStar_SMTEncoding_Util.mkApp uu____15983 in
    let uu____15996 =
      let uu____15997 =
        let uu____16004 =
          let uu____16005 =
            let uu____16016 =
              let uu____16017 =
                let uu____16022 =
                  let uu____16023 =
                    let uu____16034 =
                      let uu____16039 =
                        let uu____16042 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16042] in
                      [uu____16039] in
                    let uu____16047 =
                      let uu____16048 =
                        let uu____16053 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16053, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16048 in
                    (uu____16034, [xx1], uu____16047) in
                  FStar_SMTEncoding_Util.mkForall uu____16023 in
                (uu____16022, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16017 in
            ([[l_forall_a_b]], [aa; bb], uu____16016) in
          FStar_SMTEncoding_Util.mkForall uu____16005 in
        (uu____16004, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15997 in
    [uu____15996] in
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
      let uu____16135 =
        let uu____16142 =
          let uu____16145 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16145] in
        ("Valid", uu____16142) in
      FStar_SMTEncoding_Util.mkApp uu____16135 in
    let uu____16148 =
      let uu____16149 =
        let uu____16156 =
          let uu____16157 =
            let uu____16168 =
              let uu____16169 =
                let uu____16174 =
                  let uu____16175 =
                    let uu____16186 =
                      let uu____16191 =
                        let uu____16194 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16194] in
                      [uu____16191] in
                    let uu____16199 =
                      let uu____16200 =
                        let uu____16205 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16205, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16200 in
                    (uu____16186, [xx1], uu____16199) in
                  FStar_SMTEncoding_Util.mkExists uu____16175 in
                (uu____16174, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16169 in
            ([[l_exists_a_b]], [aa; bb], uu____16168) in
          FStar_SMTEncoding_Util.mkForall uu____16157 in
        (uu____16156, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16149 in
    [uu____16148] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16265 =
      let uu____16266 =
        let uu____16273 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16274 = varops.mk_unique "typing_range_const" in
        (uu____16273, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16274) in
      FStar_SMTEncoding_Util.mkAssume uu____16266 in
    [uu____16265] in
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
        let uu____16308 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16308 x1 t in
      let uu____16309 =
        let uu____16320 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16320) in
      FStar_SMTEncoding_Util.mkForall uu____16309 in
    let uu____16343 =
      let uu____16344 =
        let uu____16351 =
          let uu____16352 =
            let uu____16363 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16363) in
          FStar_SMTEncoding_Util.mkForall uu____16352 in
        (uu____16351,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16344 in
    [uu____16343] in
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
          let uu____16687 =
            FStar_Util.find_opt
              (fun uu____16713  ->
                 match uu____16713 with
                 | (l,uu____16725) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16687 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16750,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16789 = encode_function_type_as_formula t env in
        match uu____16789 with
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
              let uu____16835 =
                ((let uu____16838 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16838) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16835
              then
                let uu____16845 = new_term_constant_and_tok_from_lid env lid in
                match uu____16845 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16864 =
                        let uu____16865 = FStar_Syntax_Subst.compress t_norm in
                        uu____16865.FStar_Syntax_Syntax.n in
                      match uu____16864 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16871) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16901  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16906 -> [] in
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
                (let uu____16920 = prims.is lid in
                 if uu____16920
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16928 = prims.mk lid vname in
                   match uu____16928 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16952 =
                      let uu____16963 = curried_arrow_formals_comp t_norm in
                      match uu____16963 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16981 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16981
                            then
                              let uu____16982 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___164_16985 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___164_16985.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___164_16985.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___164_16985.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___164_16985.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___164_16985.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___164_16985.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___164_16985.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___164_16985.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___164_16985.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___164_16985.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___164_16985.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___164_16985.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___164_16985.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___164_16985.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___164_16985.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___164_16985.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___164_16985.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___164_16985.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___164_16985.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___164_16985.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___164_16985.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___164_16985.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___164_16985.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___164_16985.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___164_16985.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___164_16985.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___164_16985.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___164_16985.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___164_16985.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___164_16985.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___164_16985.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___164_16985.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16982
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16997 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16997)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16952 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17042 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17042 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17063 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___136_17105  ->
                                       match uu___136_17105 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17109 =
                                             FStar_Util.prefix vars in
                                           (match uu____17109 with
                                            | (uu____17130,(xxsym,uu____17132))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17150 =
                                                  let uu____17151 =
                                                    let uu____17158 =
                                                      let uu____17159 =
                                                        let uu____17170 =
                                                          let uu____17171 =
                                                            let uu____17176 =
                                                              let uu____17177
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17177 in
                                                            (vapp,
                                                              uu____17176) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17171 in
                                                        ([[vapp]], vars,
                                                          uu____17170) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17159 in
                                                    (uu____17158,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17151 in
                                                [uu____17150])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17196 =
                                             FStar_Util.prefix vars in
                                           (match uu____17196 with
                                            | (uu____17217,(xxsym,uu____17219))
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
                                                let uu____17242 =
                                                  let uu____17243 =
                                                    let uu____17250 =
                                                      let uu____17251 =
                                                        let uu____17262 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17262) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17251 in
                                                    (uu____17250,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17243 in
                                                [uu____17242])
                                       | uu____17279 -> [])) in
                             let uu____17280 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17280 with
                              | (vars,guards,env',decls1,uu____17307) ->
                                  let uu____17320 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17329 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17329, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17331 =
                                          encode_formula p env' in
                                        (match uu____17331 with
                                         | (g,ds) ->
                                             let uu____17342 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17342,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17320 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17355 =
                                           let uu____17362 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17362) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17355 in
                                       let uu____17371 =
                                         let vname_decl =
                                           let uu____17379 =
                                             let uu____17390 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17400  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17390,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17379 in
                                         let uu____17409 =
                                           let env2 =
                                             let uu___165_17415 = env1 in
                                             {
                                               bindings =
                                                 (uu___165_17415.bindings);
                                               depth = (uu___165_17415.depth);
                                               tcenv = (uu___165_17415.tcenv);
                                               warn = (uu___165_17415.warn);
                                               cache = (uu___165_17415.cache);
                                               nolabels =
                                                 (uu___165_17415.nolabels);
                                               use_zfuel_name =
                                                 (uu___165_17415.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___165_17415.current_module_name)
                                             } in
                                           let uu____17416 =
                                             let uu____17417 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17417 in
                                           if uu____17416
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17409 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17432::uu____17433 ->
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
                                                     let uu____17473 =
                                                       let uu____17484 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17484) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17473 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17511 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17514 =
                                               match formals with
                                               | [] ->
                                                   let uu____17531 =
                                                     let uu____17532 =
                                                       let uu____17535 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17535 in
                                                     push_free_var env1 lid
                                                       vname uu____17532 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17531)
                                               | uu____17540 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17547 =
                                                       let uu____17554 =
                                                         let uu____17555 =
                                                           let uu____17566 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17566) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17555 in
                                                       (uu____17554,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17547 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17514 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17371 with
                                        | (decls2,env2) ->
                                            let uu____17609 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17617 =
                                                encode_term res_t1 env' in
                                              match uu____17617 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17630 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17630, decls) in
                                            (match uu____17609 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17641 =
                                                     let uu____17648 =
                                                       let uu____17649 =
                                                         let uu____17660 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17660) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17649 in
                                                     (uu____17648,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17641 in
                                                 let freshness =
                                                   let uu____17676 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17676
                                                   then
                                                     let uu____17681 =
                                                       let uu____17682 =
                                                         let uu____17693 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17704 =
                                                           varops.next_id () in
                                                         (vname, uu____17693,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17704) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17682 in
                                                     let uu____17707 =
                                                       let uu____17710 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17710] in
                                                     uu____17681 ::
                                                       uu____17707
                                                   else [] in
                                                 let g =
                                                   let uu____17715 =
                                                     let uu____17718 =
                                                       let uu____17721 =
                                                         let uu____17724 =
                                                           let uu____17727 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17727 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17724 in
                                                       FStar_List.append
                                                         decls3 uu____17721 in
                                                     FStar_List.append decls2
                                                       uu____17718 in
                                                   FStar_List.append decls11
                                                     uu____17715 in
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
          let uu____17762 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17762 with
          | FStar_Pervasives_Native.None  ->
              let uu____17799 = encode_free_var false env x t t_norm [] in
              (match uu____17799 with
               | (decls,env1) ->
                   let uu____17826 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17826 with
                    | (n1,x',uu____17853) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17874) ->
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
            let uu____17934 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17934 with
            | (decls,env1) ->
                let uu____17953 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17953
                then
                  let uu____17960 =
                    let uu____17963 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17963 in
                  (uu____17960, env1)
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
             (fun uu____18018  ->
                fun lb  ->
                  match uu____18018 with
                  | (decls,env1) ->
                      let uu____18038 =
                        let uu____18045 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18045
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18038 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18067 = FStar_Syntax_Util.head_and_args t in
    match uu____18067 with
    | (hd1,args) ->
        let uu____18104 =
          let uu____18105 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18105.FStar_Syntax_Syntax.n in
        (match uu____18104 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18109,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18128 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18153  ->
      fun quals  ->
        match uu____18153 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18229 = FStar_Util.first_N nbinders formals in
              match uu____18229 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18310  ->
                         fun uu____18311  ->
                           match (uu____18310, uu____18311) with
                           | ((formal,uu____18329),(binder,uu____18331)) ->
                               let uu____18340 =
                                 let uu____18347 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18347) in
                               FStar_Syntax_Syntax.NT uu____18340) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18355 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18386  ->
                              match uu____18386 with
                              | (x,i) ->
                                  let uu____18397 =
                                    let uu___166_18398 = x in
                                    let uu____18399 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___166_18398.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___166_18398.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18399
                                    } in
                                  (uu____18397, i))) in
                    FStar_All.pipe_right uu____18355
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18417 =
                      let uu____18418 = FStar_Syntax_Subst.compress body in
                      let uu____18419 =
                        let uu____18420 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18420 in
                      FStar_Syntax_Syntax.extend_app_n uu____18418
                        uu____18419 in
                    uu____18417 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18481 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18481
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___167_18484 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___167_18484.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___167_18484.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___167_18484.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___167_18484.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___167_18484.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___167_18484.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___167_18484.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___167_18484.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___167_18484.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___167_18484.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___167_18484.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___167_18484.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___167_18484.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___167_18484.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___167_18484.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___167_18484.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___167_18484.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___167_18484.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___167_18484.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___167_18484.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___167_18484.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___167_18484.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___167_18484.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___167_18484.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___167_18484.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___167_18484.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___167_18484.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___167_18484.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___167_18484.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___167_18484.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___167_18484.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___167_18484.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18517 = FStar_Syntax_Util.abs_formals e in
                match uu____18517 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18581::uu____18582 ->
                         let uu____18597 =
                           let uu____18598 =
                             let uu____18601 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18601 in
                           uu____18598.FStar_Syntax_Syntax.n in
                         (match uu____18597 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18644 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18644 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18686 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18686
                                   then
                                     let uu____18721 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18721 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18815  ->
                                                   fun uu____18816  ->
                                                     match (uu____18815,
                                                             uu____18816)
                                                     with
                                                     | ((x,uu____18834),
                                                        (b,uu____18836)) ->
                                                         let uu____18845 =
                                                           let uu____18852 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18852) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18845)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18854 =
                                            let uu____18875 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18875) in
                                          (uu____18854, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18943 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18943 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19032) ->
                              let uu____19037 =
                                let uu____19058 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19058 in
                              (uu____19037, true)
                          | uu____19123 when Prims.op_Negation norm1 ->
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
                          | uu____19125 ->
                              let uu____19126 =
                                let uu____19127 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19128 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19127
                                  uu____19128 in
                              failwith uu____19126)
                     | uu____19153 ->
                         let uu____19154 =
                           let uu____19155 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19155.FStar_Syntax_Syntax.n in
                         (match uu____19154 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19200 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19200 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19232 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19232 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19315 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19371 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19371
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19383 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19477  ->
                            fun lb  ->
                              match uu____19477 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19572 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19572
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19575 =
                                      let uu____19590 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19590
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19575 with
                                    | (tok,decl,env2) ->
                                        let uu____19636 =
                                          let uu____19649 =
                                            let uu____19660 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19660, tok) in
                                          uu____19649 :: toks in
                                        (uu____19636, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19383 with
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
                        | uu____19843 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19851 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19851 vars)
                            else
                              (let uu____19853 =
                                 let uu____19860 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19860) in
                               FStar_SMTEncoding_Util.mkApp uu____19853) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19942;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19944;
                             FStar_Syntax_Syntax.lbeff = uu____19945;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20008 =
                              let uu____20015 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20015 with
                              | (tcenv',uu____20033,e_t) ->
                                  let uu____20039 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20050 -> failwith "Impossible" in
                                  (match uu____20039 with
                                   | (e1,t_norm1) ->
                                       ((let uu___170_20066 = env2 in
                                         {
                                           bindings =
                                             (uu___170_20066.bindings);
                                           depth = (uu___170_20066.depth);
                                           tcenv = tcenv';
                                           warn = (uu___170_20066.warn);
                                           cache = (uu___170_20066.cache);
                                           nolabels =
                                             (uu___170_20066.nolabels);
                                           use_zfuel_name =
                                             (uu___170_20066.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___170_20066.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___170_20066.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20008 with
                             | (env',e1,t_norm1) ->
                                 let uu____20076 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20076 with
                                  | ((binders,body,uu____20097,uu____20098),curry)
                                      ->
                                      ((let uu____20109 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20109
                                        then
                                          let uu____20110 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20111 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20110 uu____20111
                                        else ());
                                       (let uu____20113 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20113 with
                                        | (vars,guards,env'1,binder_decls,uu____20140)
                                            ->
                                            let body1 =
                                              let uu____20154 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20154
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20157 =
                                              let uu____20166 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20166
                                              then
                                                let uu____20177 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20178 =
                                                  encode_formula body1 env'1 in
                                                (uu____20177, uu____20178)
                                              else
                                                (let uu____20188 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20188)) in
                                            (match uu____20157 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20211 =
                                                     let uu____20218 =
                                                       let uu____20219 =
                                                         let uu____20230 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20230) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20219 in
                                                     let uu____20241 =
                                                       let uu____20244 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20244 in
                                                     (uu____20218,
                                                       uu____20241,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20211 in
                                                 let uu____20247 =
                                                   let uu____20250 =
                                                     let uu____20253 =
                                                       let uu____20256 =
                                                         let uu____20259 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20259 in
                                                       FStar_List.append
                                                         decls2 uu____20256 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20253 in
                                                   FStar_List.append decls1
                                                     uu____20250 in
                                                 (uu____20247, env2))))))
                        | uu____20264 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20349 = varops.fresh "fuel" in
                          (uu____20349, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20352 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20440  ->
                                  fun uu____20441  ->
                                    match (uu____20440, uu____20441) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20589 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20589 in
                                        let gtok =
                                          let uu____20591 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20591 in
                                        let env4 =
                                          let uu____20593 =
                                            let uu____20596 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20596 in
                                          push_free_var env3 flid gtok
                                            uu____20593 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20352 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20752 t_norm
                              uu____20754 =
                              match (uu____20752, uu____20754) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20798;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20799;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20827 =
                                    let uu____20834 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20834 with
                                    | (tcenv',uu____20856,e_t) ->
                                        let uu____20862 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20873 ->
                                              failwith "Impossible" in
                                        (match uu____20862 with
                                         | (e1,t_norm1) ->
                                             ((let uu___171_20889 = env3 in
                                               {
                                                 bindings =
                                                   (uu___171_20889.bindings);
                                                 depth =
                                                   (uu___171_20889.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___171_20889.warn);
                                                 cache =
                                                   (uu___171_20889.cache);
                                                 nolabels =
                                                   (uu___171_20889.nolabels);
                                                 use_zfuel_name =
                                                   (uu___171_20889.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___171_20889.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___171_20889.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20827 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20904 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20904
                                         then
                                           let uu____20905 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20906 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20907 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20905 uu____20906
                                             uu____20907
                                         else ());
                                        (let uu____20909 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20909 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20946 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20946
                                               then
                                                 let uu____20947 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20948 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20949 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20950 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20947 uu____20948
                                                   uu____20949 uu____20950
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20954 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20954 with
                                               | (vars,guards,env'1,binder_decls,uu____20985)
                                                   ->
                                                   let decl_g =
                                                     let uu____20999 =
                                                       let uu____21010 =
                                                         let uu____21013 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21013 in
                                                       (g, uu____21010,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20999 in
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
                                                     let uu____21038 =
                                                       let uu____21045 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21045) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21038 in
                                                   let gsapp =
                                                     let uu____21055 =
                                                       let uu____21062 =
                                                         let uu____21065 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21065 ::
                                                           vars_tm in
                                                       (g, uu____21062) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21055 in
                                                   let gmax =
                                                     let uu____21071 =
                                                       let uu____21078 =
                                                         let uu____21081 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21081 ::
                                                           vars_tm in
                                                       (g, uu____21078) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21071 in
                                                   let body1 =
                                                     let uu____21087 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21087
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21089 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21089 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21107 =
                                                            let uu____21114 =
                                                              let uu____21115
                                                                =
                                                                let uu____21130
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
                                                                  uu____21130) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21115 in
                                                            let uu____21151 =
                                                              let uu____21154
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21154 in
                                                            (uu____21114,
                                                              uu____21151,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21107 in
                                                        let eqn_f =
                                                          let uu____21158 =
                                                            let uu____21165 =
                                                              let uu____21166
                                                                =
                                                                let uu____21177
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21177) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21166 in
                                                            (uu____21165,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21158 in
                                                        let eqn_g' =
                                                          let uu____21191 =
                                                            let uu____21198 =
                                                              let uu____21199
                                                                =
                                                                let uu____21210
                                                                  =
                                                                  let uu____21211
                                                                    =
                                                                    let uu____21216
                                                                    =
                                                                    let uu____21217
                                                                    =
                                                                    let uu____21224
                                                                    =
                                                                    let uu____21227
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21227
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21224) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21217 in
                                                                    (gsapp,
                                                                    uu____21216) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21211 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21210) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21199 in
                                                            (uu____21198,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21191 in
                                                        let uu____21250 =
                                                          let uu____21259 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21259
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21288)
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
                                                                  let uu____21313
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21313
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21318
                                                                  =
                                                                  let uu____21325
                                                                    =
                                                                    let uu____21326
                                                                    =
                                                                    let uu____21337
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21337) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21326 in
                                                                  (uu____21325,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21318 in
                                                              let uu____21358
                                                                =
                                                                let uu____21365
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21365
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21378
                                                                    =
                                                                    let uu____21381
                                                                    =
                                                                    let uu____21382
                                                                    =
                                                                    let uu____21389
                                                                    =
                                                                    let uu____21390
                                                                    =
                                                                    let uu____21401
                                                                    =
                                                                    let uu____21402
                                                                    =
                                                                    let uu____21407
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21407,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21402 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21401) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21390 in
                                                                    (uu____21389,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21382 in
                                                                    [uu____21381] in
                                                                    (d3,
                                                                    uu____21378) in
                                                              (match uu____21358
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21250
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
                            let uu____21472 =
                              let uu____21485 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21564  ->
                                   fun uu____21565  ->
                                     match (uu____21564, uu____21565) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21720 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21720 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21485 in
                            (match uu____21472 with
                             | (decls2,eqns,env01) ->
                                 let uu____21793 =
                                   let isDeclFun uu___137_21805 =
                                     match uu___137_21805 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21806 -> true
                                     | uu____21817 -> false in
                                   let uu____21818 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21818
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21793 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21858 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___138_21862  ->
                                 match uu___138_21862 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21863 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21869 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21869))) in
                      if uu____21858
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
                   let uu____21921 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21921
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
        let uu____21970 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21970 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21974 = encode_sigelt' env se in
      match uu____21974 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21990 =
                  let uu____21991 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21991 in
                [uu____21990]
            | uu____21992 ->
                let uu____21993 =
                  let uu____21996 =
                    let uu____21997 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21997 in
                  uu____21996 :: g in
                let uu____21998 =
                  let uu____22001 =
                    let uu____22002 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22002 in
                  [uu____22001] in
                FStar_List.append uu____21993 uu____21998 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22015 =
          let uu____22016 = FStar_Syntax_Subst.compress t in
          uu____22016.FStar_Syntax_Syntax.n in
        match uu____22015 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22020)) -> s = "opaque_to_smt"
        | uu____22021 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22026 =
          let uu____22027 = FStar_Syntax_Subst.compress t in
          uu____22027.FStar_Syntax_Syntax.n in
        match uu____22026 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22031)) -> s = "uninterpreted_by_smt"
        | uu____22032 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22037 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22042 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22045 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22048 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22063 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22067 =
            let uu____22068 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22068 Prims.op_Negation in
          if uu____22067
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22094 ->
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
               let uu____22114 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22114 with
               | (aname,atok,env2) ->
                   let uu____22130 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22130 with
                    | (formals,uu____22148) ->
                        let uu____22161 =
                          let uu____22166 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22166 env2 in
                        (match uu____22161 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22178 =
                                 let uu____22179 =
                                   let uu____22190 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22206  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22190,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22179 in
                               [uu____22178;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22219 =
                               let aux uu____22271 uu____22272 =
                                 match (uu____22271, uu____22272) with
                                 | ((bv,uu____22324),(env3,acc_sorts,acc)) ->
                                     let uu____22362 = gen_term_var env3 bv in
                                     (match uu____22362 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22219 with
                              | (uu____22434,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22457 =
                                      let uu____22464 =
                                        let uu____22465 =
                                          let uu____22476 =
                                            let uu____22477 =
                                              let uu____22482 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22482) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22477 in
                                          ([[app]], xs_sorts, uu____22476) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22465 in
                                      (uu____22464,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22457 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22502 =
                                      let uu____22509 =
                                        let uu____22510 =
                                          let uu____22521 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22521) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22510 in
                                      (uu____22509,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22502 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22540 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22540 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22568,uu____22569)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22570 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22570 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22587,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22593 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___139_22597  ->
                      match uu___139_22597 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22598 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22603 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22604 -> false)) in
            Prims.op_Negation uu____22593 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22613 =
               let uu____22620 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22620 env fv t quals in
             match uu____22613 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22635 =
                   let uu____22638 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22638 in
                 (uu____22635, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22646 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22646 with
           | (uu____22655,f1) ->
               let uu____22657 = encode_formula f1 env in
               (match uu____22657 with
                | (f2,decls) ->
                    let g =
                      let uu____22671 =
                        let uu____22672 =
                          let uu____22679 =
                            let uu____22682 =
                              let uu____22683 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22683 in
                            FStar_Pervasives_Native.Some uu____22682 in
                          let uu____22684 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22679, uu____22684) in
                        FStar_SMTEncoding_Util.mkAssume uu____22672 in
                      [uu____22671] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22690) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22702 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22720 =
                       let uu____22723 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22723.FStar_Syntax_Syntax.fv_name in
                     uu____22720.FStar_Syntax_Syntax.v in
                   let uu____22724 =
                     let uu____22725 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22725 in
                   if uu____22724
                   then
                     let val_decl =
                       let uu___174_22753 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___174_22753.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___174_22753.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___174_22753.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22758 = encode_sigelt' env1 val_decl in
                     match uu____22758 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22702 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22786,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22788;
                          FStar_Syntax_Syntax.lbtyp = uu____22789;
                          FStar_Syntax_Syntax.lbeff = uu____22790;
                          FStar_Syntax_Syntax.lbdef = uu____22791;_}::[]),uu____22792)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22811 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22811 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22840 =
                   let uu____22843 =
                     let uu____22844 =
                       let uu____22851 =
                         let uu____22852 =
                           let uu____22863 =
                             let uu____22864 =
                               let uu____22869 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22869) in
                             FStar_SMTEncoding_Util.mkEq uu____22864 in
                           ([[b2t_x]], [xx], uu____22863) in
                         FStar_SMTEncoding_Util.mkForall uu____22852 in
                       (uu____22851,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22844 in
                   [uu____22843] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22840 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22902,uu____22903) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___140_22912  ->
                  match uu___140_22912 with
                  | FStar_Syntax_Syntax.Discriminator uu____22913 -> true
                  | uu____22914 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22917,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22928 =
                     let uu____22929 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22929.FStar_Ident.idText in
                   uu____22928 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___141_22933  ->
                     match uu___141_22933 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22934 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22938) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___142_22955  ->
                  match uu___142_22955 with
                  | FStar_Syntax_Syntax.Projector uu____22956 -> true
                  | uu____22961 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22964 = try_lookup_free_var env l in
          (match uu____22964 with
           | FStar_Pervasives_Native.Some uu____22971 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___175_22975 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___175_22975.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___175_22975.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___175_22975.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22982) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23000) ->
          let uu____23009 = encode_sigelts env ses in
          (match uu____23009 with
           | (g,env1) ->
               let uu____23026 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___143_23049  ->
                         match uu___143_23049 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23050;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23051;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23052;_}
                             -> false
                         | uu____23055 -> true)) in
               (match uu____23026 with
                | (g',inversions) ->
                    let uu____23070 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___144_23091  ->
                              match uu___144_23091 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23092 ->
                                  true
                              | uu____23103 -> false)) in
                    (match uu____23070 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23121,tps,k,uu____23124,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___145_23141  ->
                    match uu___145_23141 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23142 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23151 = c in
              match uu____23151 with
              | (name,args,uu____23156,uu____23157,uu____23158) ->
                  let uu____23163 =
                    let uu____23164 =
                      let uu____23175 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23192  ->
                                match uu____23192 with
                                | (uu____23199,sort,uu____23201) -> sort)) in
                      (name, uu____23175, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23164 in
                  [uu____23163]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23228 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23234 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23234 FStar_Option.isNone)) in
            if uu____23228
            then []
            else
              (let uu____23266 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23266 with
               | (xxsym,xx) ->
                   let uu____23275 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23314  ->
                             fun l  ->
                               match uu____23314 with
                               | (out,decls) ->
                                   let uu____23334 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23334 with
                                    | (uu____23345,data_t) ->
                                        let uu____23347 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23347 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23393 =
                                                 let uu____23394 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23394.FStar_Syntax_Syntax.n in
                                               match uu____23393 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23405,indices) ->
                                                   indices
                                               | uu____23427 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23451  ->
                                                         match uu____23451
                                                         with
                                                         | (x,uu____23457) ->
                                                             let uu____23458
                                                               =
                                                               let uu____23459
                                                                 =
                                                                 let uu____23466
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23466,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23459 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23458)
                                                    env) in
                                             let uu____23469 =
                                               encode_args indices env1 in
                                             (match uu____23469 with
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
                                                      let uu____23495 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23511
                                                                 =
                                                                 let uu____23516
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23516,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23511)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23495
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23519 =
                                                      let uu____23520 =
                                                        let uu____23525 =
                                                          let uu____23526 =
                                                            let uu____23531 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23531,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23526 in
                                                        (out, uu____23525) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23520 in
                                                    (uu____23519,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23275 with
                    | (data_ax,decls) ->
                        let uu____23544 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23544 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23555 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23555 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23559 =
                                 let uu____23566 =
                                   let uu____23567 =
                                     let uu____23578 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23593 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23578,
                                       uu____23593) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23567 in
                                 let uu____23608 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23566,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23608) in
                               FStar_SMTEncoding_Util.mkAssume uu____23559 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23611 =
            let uu____23624 =
              let uu____23625 = FStar_Syntax_Subst.compress k in
              uu____23625.FStar_Syntax_Syntax.n in
            match uu____23624 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23670 -> (tps, k) in
          (match uu____23611 with
           | (formals,res) ->
               let uu____23693 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23693 with
                | (formals1,res1) ->
                    let uu____23704 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23704 with
                     | (vars,guards,env',binder_decls,uu____23729) ->
                         let uu____23742 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23742 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23761 =
                                  let uu____23768 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23768) in
                                FStar_SMTEncoding_Util.mkApp uu____23761 in
                              let uu____23777 =
                                let tname_decl =
                                  let uu____23787 =
                                    let uu____23788 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23820  ->
                                              match uu____23820 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23833 = varops.next_id () in
                                    (tname, uu____23788,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23833, false) in
                                  constructor_or_logic_type_decl uu____23787 in
                                let uu____23842 =
                                  match vars with
                                  | [] ->
                                      let uu____23855 =
                                        let uu____23856 =
                                          let uu____23859 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23859 in
                                        push_free_var env1 t tname
                                          uu____23856 in
                                      ([], uu____23855)
                                  | uu____23866 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23875 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23875 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23889 =
                                          let uu____23896 =
                                            let uu____23897 =
                                              let uu____23912 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23912) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23897 in
                                          (uu____23896,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23889 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23842 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23777 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23952 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23952 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23970 =
                                               let uu____23971 =
                                                 let uu____23978 =
                                                   let uu____23979 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23979 in
                                                 (uu____23978,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23971 in
                                             [uu____23970]
                                           else [] in
                                         let uu____23983 =
                                           let uu____23986 =
                                             let uu____23989 =
                                               let uu____23990 =
                                                 let uu____23997 =
                                                   let uu____23998 =
                                                     let uu____24009 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24009) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23998 in
                                                 (uu____23997,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23990 in
                                             [uu____23989] in
                                           FStar_List.append karr uu____23986 in
                                         FStar_List.append decls1 uu____23983 in
                                   let aux =
                                     let uu____24025 =
                                       let uu____24028 =
                                         inversion_axioms tapp vars in
                                       let uu____24031 =
                                         let uu____24034 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24034] in
                                       FStar_List.append uu____24028
                                         uu____24031 in
                                     FStar_List.append kindingAx uu____24025 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24041,uu____24042,uu____24043,uu____24044,uu____24045)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24053,t,uu____24055,n_tps,uu____24057) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24065 = new_term_constant_and_tok_from_lid env d in
          (match uu____24065 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24082 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24082 with
                | (formals,t_res) ->
                    let uu____24117 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24117 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24131 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24131 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24201 =
                                            mk_term_projector_name d x in
                                          (uu____24201,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24203 =
                                  let uu____24222 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24222, true) in
                                FStar_All.pipe_right uu____24203
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
                              let uu____24261 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24261 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24273::uu____24274 ->
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
                                         let uu____24319 =
                                           let uu____24330 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24330) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24319
                                     | uu____24355 -> tok_typing in
                                   let uu____24364 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24364 with
                                    | (vars',guards',env'',decls_formals,uu____24389)
                                        ->
                                        let uu____24402 =
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
                                        (match uu____24402 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24433 ->
                                                   let uu____24440 =
                                                     let uu____24441 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24441 in
                                                   [uu____24440] in
                                             let encode_elim uu____24451 =
                                               let uu____24452 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24452 with
                                               | (head1,args) ->
                                                   let uu____24495 =
                                                     let uu____24496 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24496.FStar_Syntax_Syntax.n in
                                                   (match uu____24495 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24506;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24507;_},uu____24508)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24514 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24514
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
                                                                 | uu____24557
                                                                    ->
                                                                    let uu____24558
                                                                    =
                                                                    let uu____24559
                                                                    =
                                                                    let uu____24564
                                                                    =
                                                                    let uu____24565
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24565 in
                                                                    (uu____24564,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24559 in
                                                                    FStar_Exn.raise
                                                                    uu____24558 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24581
                                                                    =
                                                                    let uu____24582
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24582 in
                                                                    if
                                                                    uu____24581
                                                                    then
                                                                    let uu____24595
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24595]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24597
                                                               =
                                                               let uu____24610
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24660
                                                                     ->
                                                                    fun
                                                                    uu____24661
                                                                     ->
                                                                    match 
                                                                    (uu____24660,
                                                                    uu____24661)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24756
                                                                    =
                                                                    let uu____24763
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24763 in
                                                                    (match uu____24756
                                                                    with
                                                                    | 
                                                                    (uu____24776,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24784
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24784
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24786
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24786
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
                                                                 uu____24610 in
                                                             (match uu____24597
                                                              with
                                                              | (uu____24801,arg_vars,elim_eqns_or_guards,uu____24804)
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
                                                                    let uu____24834
                                                                    =
                                                                    let uu____24841
                                                                    =
                                                                    let uu____24842
                                                                    =
                                                                    let uu____24853
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24864
                                                                    =
                                                                    let uu____24865
                                                                    =
                                                                    let uu____24870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24870) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24865 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24853,
                                                                    uu____24864) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24842 in
                                                                    (uu____24841,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24834 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24893
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24893,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24895
                                                                    =
                                                                    let uu____24902
                                                                    =
                                                                    let uu____24903
                                                                    =
                                                                    let uu____24914
                                                                    =
                                                                    let uu____24919
                                                                    =
                                                                    let uu____24922
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24922] in
                                                                    [uu____24919] in
                                                                    let uu____24927
                                                                    =
                                                                    let uu____24928
                                                                    =
                                                                    let uu____24933
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24934
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24933,
                                                                    uu____24934) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24928 in
                                                                    (uu____24914,
                                                                    [x],
                                                                    uu____24927) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24903 in
                                                                    let uu____24953
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24902,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24953) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24895
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24960
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
                                                                    (let uu____24988
                                                                    =
                                                                    let uu____24989
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24989
                                                                    dapp1 in
                                                                    [uu____24988]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24960
                                                                    FStar_List.flatten in
                                                                    let uu____24996
                                                                    =
                                                                    let uu____25003
                                                                    =
                                                                    let uu____25004
                                                                    =
                                                                    let uu____25015
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25026
                                                                    =
                                                                    let uu____25027
                                                                    =
                                                                    let uu____25032
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25032) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25027 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25015,
                                                                    uu____25026) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25004 in
                                                                    (uu____25003,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24996) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25053 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25053
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
                                                                 | uu____25096
                                                                    ->
                                                                    let uu____25097
                                                                    =
                                                                    let uu____25098
                                                                    =
                                                                    let uu____25103
                                                                    =
                                                                    let uu____25104
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25104 in
                                                                    (uu____25103,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25098 in
                                                                    FStar_Exn.raise
                                                                    uu____25097 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25120
                                                                    =
                                                                    let uu____25121
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25121 in
                                                                    if
                                                                    uu____25120
                                                                    then
                                                                    let uu____25134
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25134]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25136
                                                               =
                                                               let uu____25149
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25199
                                                                     ->
                                                                    fun
                                                                    uu____25200
                                                                     ->
                                                                    match 
                                                                    (uu____25199,
                                                                    uu____25200)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25295
                                                                    =
                                                                    let uu____25302
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25302 in
                                                                    (match uu____25295
                                                                    with
                                                                    | 
                                                                    (uu____25315,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25323
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25323
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25325
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25325
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
                                                                 uu____25149 in
                                                             (match uu____25136
                                                              with
                                                              | (uu____25340,arg_vars,elim_eqns_or_guards,uu____25343)
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
                                                                    let uu____25373
                                                                    =
                                                                    let uu____25380
                                                                    =
                                                                    let uu____25381
                                                                    =
                                                                    let uu____25392
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25403
                                                                    =
                                                                    let uu____25404
                                                                    =
                                                                    let uu____25409
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25409) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25404 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25392,
                                                                    uu____25403) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25381 in
                                                                    (uu____25380,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25373 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25432
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25432,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25434
                                                                    =
                                                                    let uu____25441
                                                                    =
                                                                    let uu____25442
                                                                    =
                                                                    let uu____25453
                                                                    =
                                                                    let uu____25458
                                                                    =
                                                                    let uu____25461
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25461] in
                                                                    [uu____25458] in
                                                                    let uu____25466
                                                                    =
                                                                    let uu____25467
                                                                    =
                                                                    let uu____25472
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25473
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25472,
                                                                    uu____25473) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25467 in
                                                                    (uu____25453,
                                                                    [x],
                                                                    uu____25466) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25442 in
                                                                    let uu____25492
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25441,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25492) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25434
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25499
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
                                                                    (let uu____25527
                                                                    =
                                                                    let uu____25528
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25528
                                                                    dapp1 in
                                                                    [uu____25527]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25499
                                                                    FStar_List.flatten in
                                                                    let uu____25535
                                                                    =
                                                                    let uu____25542
                                                                    =
                                                                    let uu____25543
                                                                    =
                                                                    let uu____25554
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25565
                                                                    =
                                                                    let uu____25566
                                                                    =
                                                                    let uu____25571
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25571) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25566 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25554,
                                                                    uu____25565) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25543 in
                                                                    (uu____25542,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25535) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25590 ->
                                                        ((let uu____25592 =
                                                            let uu____25593 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25594 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25593
                                                              uu____25594 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25592);
                                                         ([], []))) in
                                             let uu____25599 = encode_elim () in
                                             (match uu____25599 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25619 =
                                                      let uu____25622 =
                                                        let uu____25625 =
                                                          let uu____25628 =
                                                            let uu____25631 =
                                                              let uu____25632
                                                                =
                                                                let uu____25643
                                                                  =
                                                                  let uu____25646
                                                                    =
                                                                    let uu____25647
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25647 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25646 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25643) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25632 in
                                                            [uu____25631] in
                                                          let uu____25652 =
                                                            let uu____25655 =
                                                              let uu____25658
                                                                =
                                                                let uu____25661
                                                                  =
                                                                  let uu____25664
                                                                    =
                                                                    let uu____25667
                                                                    =
                                                                    let uu____25670
                                                                    =
                                                                    let uu____25671
                                                                    =
                                                                    let uu____25678
                                                                    =
                                                                    let uu____25679
                                                                    =
                                                                    let uu____25690
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25690) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25679 in
                                                                    (uu____25678,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25671 in
                                                                    let uu____25703
                                                                    =
                                                                    let uu____25706
                                                                    =
                                                                    let uu____25707
                                                                    =
                                                                    let uu____25714
                                                                    =
                                                                    let uu____25715
                                                                    =
                                                                    let uu____25726
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25737
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25726,
                                                                    uu____25737) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25715 in
                                                                    (uu____25714,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25707 in
                                                                    [uu____25706] in
                                                                    uu____25670
                                                                    ::
                                                                    uu____25703 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25667 in
                                                                  FStar_List.append
                                                                    uu____25664
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25661 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25658 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25655 in
                                                          FStar_List.append
                                                            uu____25628
                                                            uu____25652 in
                                                        FStar_List.append
                                                          decls3 uu____25625 in
                                                      FStar_List.append
                                                        decls2 uu____25622 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25619 in
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
           (fun uu____25783  ->
              fun se  ->
                match uu____25783 with
                | (g,env1) ->
                    let uu____25803 = encode_sigelt env1 se in
                    (match uu____25803 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25862 =
        match uu____25862 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25894 ->
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
                 ((let uu____25900 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25900
                   then
                     let uu____25901 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25902 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25903 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25901 uu____25902 uu____25903
                   else ());
                  (let uu____25905 = encode_term t1 env1 in
                   match uu____25905 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25921 =
                         let uu____25928 =
                           let uu____25929 =
                             let uu____25930 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25930
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25929 in
                         new_term_constant_from_string env1 x uu____25928 in
                       (match uu____25921 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25946 = FStar_Options.log_queries () in
                              if uu____25946
                              then
                                let uu____25949 =
                                  let uu____25950 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25951 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25952 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25950 uu____25951 uu____25952 in
                                FStar_Pervasives_Native.Some uu____25949
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25968,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25982 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25982 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26005,se,uu____26007) ->
                 let uu____26012 = encode_sigelt env1 se in
                 (match uu____26012 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26029,se) ->
                 let uu____26035 = encode_sigelt env1 se in
                 (match uu____26035 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26052 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26052 with | (uu____26075,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26090 'Auu____26091 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26091,'Auu____26090)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26159  ->
              match uu____26159 with
              | (l,uu____26171,uu____26172) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26218  ->
              match uu____26218 with
              | (l,uu____26232,uu____26233) ->
                  let uu____26242 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26243 =
                    let uu____26246 =
                      let uu____26247 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26247 in
                    [uu____26246] in
                  uu____26242 :: uu____26243)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26269 =
      let uu____26272 =
        let uu____26273 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26276 =
          let uu____26277 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26277 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26273;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26276
        } in
      [uu____26272] in
    FStar_ST.op_Colon_Equals last_env uu____26269
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26336 = FStar_ST.op_Bang last_env in
      match uu____26336 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26390 ->
          let uu___176_26393 = e in
          let uu____26394 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___176_26393.bindings);
            depth = (uu___176_26393.depth);
            tcenv;
            warn = (uu___176_26393.warn);
            cache = (uu___176_26393.cache);
            nolabels = (uu___176_26393.nolabels);
            use_zfuel_name = (uu___176_26393.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___176_26393.encode_non_total_function_typ);
            current_module_name = uu____26394
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26399 = FStar_ST.op_Bang last_env in
    match uu____26399 with
    | [] -> failwith "Empty env stack"
    | uu____26452::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26509  ->
    let uu____26510 = FStar_ST.op_Bang last_env in
    match uu____26510 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___177_26571 = hd1 in
          {
            bindings = (uu___177_26571.bindings);
            depth = (uu___177_26571.depth);
            tcenv = (uu___177_26571.tcenv);
            warn = (uu___177_26571.warn);
            cache = refs;
            nolabels = (uu___177_26571.nolabels);
            use_zfuel_name = (uu___177_26571.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26571.encode_non_total_function_typ);
            current_module_name = (uu___177_26571.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26625  ->
    let uu____26626 = FStar_ST.op_Bang last_env in
    match uu____26626 with
    | [] -> failwith "Popping an empty stack"
    | uu____26679::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26777::uu____26778,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___178_26786 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___178_26786.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___178_26786.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___178_26786.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26787 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26804 =
        let uu____26807 =
          let uu____26808 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26808 in
        let uu____26809 = open_fact_db_tags env in uu____26807 :: uu____26809 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26804
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
      let uu____26833 = encode_sigelt env se in
      match uu____26833 with
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
        let uu____26871 = FStar_Options.log_queries () in
        if uu____26871
        then
          let uu____26874 =
            let uu____26875 =
              let uu____26876 =
                let uu____26877 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26877 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26876 in
            FStar_SMTEncoding_Term.Caption uu____26875 in
          uu____26874 :: decls
        else decls in
      (let uu____26888 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26888
       then
         let uu____26889 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26889
       else ());
      (let env =
         let uu____26892 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26892 tcenv in
       let uu____26893 = encode_top_level_facts env se in
       match uu____26893 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26907 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26907)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26921 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26921
       then
         let uu____26922 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26922
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26957  ->
                 fun se  ->
                   match uu____26957 with
                   | (g,env2) ->
                       let uu____26977 = encode_top_level_facts env2 se in
                       (match uu____26977 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27000 =
         encode_signature
           (let uu___179_27009 = env in
            {
              bindings = (uu___179_27009.bindings);
              depth = (uu___179_27009.depth);
              tcenv = (uu___179_27009.tcenv);
              warn = false;
              cache = (uu___179_27009.cache);
              nolabels = (uu___179_27009.nolabels);
              use_zfuel_name = (uu___179_27009.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___179_27009.encode_non_total_function_typ);
              current_module_name = (uu___179_27009.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27000 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27026 = FStar_Options.log_queries () in
             if uu____27026
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___180_27034 = env1 in
               {
                 bindings = (uu___180_27034.bindings);
                 depth = (uu___180_27034.depth);
                 tcenv = (uu___180_27034.tcenv);
                 warn = true;
                 cache = (uu___180_27034.cache);
                 nolabels = (uu___180_27034.nolabels);
                 use_zfuel_name = (uu___180_27034.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___180_27034.encode_non_total_function_typ);
                 current_module_name = (uu___180_27034.current_module_name)
               });
            (let uu____27036 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27036
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
        (let uu____27091 =
           let uu____27092 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27092.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27091);
        (let env =
           let uu____27094 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27094 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27106 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27141 = aux rest in
                 (match uu____27141 with
                  | (out,rest1) ->
                      let t =
                        let uu____27171 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27171 with
                        | FStar_Pervasives_Native.Some uu____27176 ->
                            let uu____27177 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27177
                              x.FStar_Syntax_Syntax.sort
                        | uu____27178 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27182 =
                        let uu____27185 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___181_27188 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___181_27188.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___181_27188.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27185 :: out in
                      (uu____27182, rest1))
             | uu____27193 -> ([], bindings1) in
           let uu____27200 = aux bindings in
           match uu____27200 with
           | (closing,bindings1) ->
               let uu____27225 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27225, bindings1) in
         match uu____27106 with
         | (q1,bindings1) ->
             let uu____27248 =
               let uu____27253 =
                 FStar_List.filter
                   (fun uu___146_27258  ->
                      match uu___146_27258 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27259 ->
                          false
                      | uu____27266 -> true) bindings1 in
               encode_env_bindings env uu____27253 in
             (match uu____27248 with
              | (env_decls,env1) ->
                  ((let uu____27284 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27284
                    then
                      let uu____27285 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27285
                    else ());
                   (let uu____27287 = encode_formula q1 env1 in
                    match uu____27287 with
                    | (phi,qdecls) ->
                        let uu____27308 =
                          let uu____27313 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27313 phi in
                        (match uu____27308 with
                         | (labels,phi1) ->
                             let uu____27330 = encode_labels labels in
                             (match uu____27330 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27367 =
                                      let uu____27374 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27375 =
                                        varops.mk_unique "@query" in
                                      (uu____27374,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27375) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27367 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))