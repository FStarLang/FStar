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
        let id1 = next_id1 () in
        let f =
          let uu____1368 = FStar_SMTEncoding_Util.mk_String_const id1 in
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
          let uu____4522 =
            let uu____4523 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4523 in
          (uu____4522, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4544) ->
          let uu____4545 = varops.string_const s in (uu____4545, [])
      | FStar_Const.Const_range r ->
          (FStar_SMTEncoding_Term.mk_Range_const, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4554 =
            let uu____4555 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4555 in
          failwith uu____4554
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
        (let uu____4584 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4584
         then
           let uu____4585 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4585
         else ());
        (let uu____4587 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4671  ->
                   fun b  ->
                     match uu____4671 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4750 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4766 = gen_term_var env1 x in
                           match uu____4766 with
                           | (xxsym,xx,env') ->
                               let uu____4790 =
                                 let uu____4795 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4795 env1 xx in
                               (match uu____4790 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4750 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4587 with
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
          let uu____4954 = encode_term t env in
          match uu____4954 with
          | (t1,decls) ->
              let uu____4965 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4965, decls)
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
          let uu____4976 = encode_term t env in
          match uu____4976 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4991 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4991, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4993 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4993, decls))
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
        let uu____4999 = encode_args args_e env in
        match uu____4999 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5018 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____5027 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____5027 in
            let binary arg_tms1 =
              let uu____5040 =
                let uu____5041 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____5041 in
              let uu____5042 =
                let uu____5043 =
                  let uu____5044 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____5044 in
                FStar_SMTEncoding_Term.unboxInt uu____5043 in
              (uu____5040, uu____5042) in
            let mk_default uu____5050 =
              let uu____5051 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____5051 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____5102 = FStar_Options.smtencoding_l_arith_native () in
              if uu____5102
              then
                let uu____5103 = let uu____5104 = mk_args ts in op uu____5104 in
                FStar_All.pipe_right uu____5103 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____5133 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____5133
              then
                let uu____5134 = binary ts in
                match uu____5134 with
                | (t1,t2) ->
                    let uu____5141 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____5141
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5145 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____5145
                 then
                   let uu____5146 = op (binary ts) in
                   FStar_All.pipe_right uu____5146
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
            let uu____5277 =
              let uu____5286 =
                FStar_List.tryFind
                  (fun uu____5308  ->
                     match uu____5308 with
                     | (l,uu____5318) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5286 FStar_Util.must in
            (match uu____5277 with
             | (uu____5357,op) ->
                 let uu____5367 = op arg_tms in (uu____5367, decls))
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
        let uu____5375 = FStar_List.hd args_e in
        match uu____5375 with
        | (tm_sz,uu____5383) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5393 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5393 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5401 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5401);
                   t_decls) in
            let uu____5402 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5422::(sz_arg,uu____5424)::uu____5425::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5474 =
                    let uu____5477 = FStar_List.tail args_e in
                    FStar_List.tail uu____5477 in
                  let uu____5480 =
                    let uu____5483 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5483 in
                  (uu____5474, uu____5480)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5489::(sz_arg,uu____5491)::uu____5492::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5541 =
                    let uu____5542 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5542 in
                  failwith uu____5541
              | uu____5551 ->
                  let uu____5558 = FStar_List.tail args_e in
                  (uu____5558, FStar_Pervasives_Native.None) in
            (match uu____5402 with
             | (arg_tms,ext_sz) ->
                 let uu____5581 = encode_args arg_tms env in
                 (match uu____5581 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5602 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5611 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5611 in
                      let unary_arith arg_tms2 =
                        let uu____5620 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5620 in
                      let binary arg_tms2 =
                        let uu____5633 =
                          let uu____5634 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5634 in
                        let uu____5635 =
                          let uu____5636 =
                            let uu____5637 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5637 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5636 in
                        (uu____5633, uu____5635) in
                      let binary_arith arg_tms2 =
                        let uu____5652 =
                          let uu____5653 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5653 in
                        let uu____5654 =
                          let uu____5655 =
                            let uu____5656 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5656 in
                          FStar_SMTEncoding_Term.unboxInt uu____5655 in
                        (uu____5652, uu____5654) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5705 =
                          let uu____5706 = mk_args ts in op uu____5706 in
                        FStar_All.pipe_right uu____5705 resBox in
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
                        let uu____5796 =
                          let uu____5799 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5799 in
                        let uu____5801 =
                          let uu____5804 =
                            let uu____5805 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5805 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5804 in
                        mk_bv uu____5796 unary uu____5801 arg_tms2 in
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
                      let uu____5980 =
                        let uu____5989 =
                          FStar_List.tryFind
                            (fun uu____6011  ->
                               match uu____6011 with
                               | (l,uu____6021) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5989 FStar_Util.must in
                      (match uu____5980 with
                       | (uu____6062,op) ->
                           let uu____6072 = op arg_tms1 in
                           (uu____6072, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____6083 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____6083
       then
         let uu____6084 = FStar_Syntax_Print.tag_of_term t in
         let uu____6085 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____6086 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6084 uu____6085
           uu____6086
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6092 ->
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
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6126 =
             let uu____6127 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6128 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6129 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6130 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6127
               uu____6128 uu____6129 uu____6130 in
           failwith uu____6126
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6136 =
             let uu____6137 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6137 in
           failwith uu____6136
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6144) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6185;
              FStar_Syntax_Syntax.vars = uu____6186;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6203 = varops.fresh "t" in
             (uu____6203, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6206 =
               let uu____6217 =
                 let uu____6220 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6220 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6217) in
             FStar_SMTEncoding_Term.DeclFun uu____6206 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6228) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6238 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6238, [])
       | FStar_Syntax_Syntax.Tm_type uu____6241 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6245) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6270 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6270 with
            | (binders1,res) ->
                let uu____6281 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6281
                then
                  let uu____6286 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6286 with
                   | (vars,guards,env',decls,uu____6311) ->
                       let fsym =
                         let uu____6329 = varops.fresh "f" in
                         (uu____6329, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6332 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___156_6341 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___156_6341.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___156_6341.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___156_6341.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___156_6341.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___156_6341.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___156_6341.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___156_6341.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___156_6341.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___156_6341.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___156_6341.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___156_6341.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___156_6341.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___156_6341.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___156_6341.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___156_6341.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___156_6341.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___156_6341.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___156_6341.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___156_6341.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___156_6341.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___156_6341.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___156_6341.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___156_6341.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___156_6341.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___156_6341.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___156_6341.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___156_6341.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___156_6341.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___156_6341.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___156_6341.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___156_6341.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___156_6341.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6332 with
                        | (pre_opt,res_t) ->
                            let uu____6352 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6352 with
                             | (res_pred,decls') ->
                                 let uu____6363 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6376 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6376, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6380 =
                                         encode_formula pre env' in
                                       (match uu____6380 with
                                        | (guard,decls0) ->
                                            let uu____6393 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6393, decls0)) in
                                 (match uu____6363 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6405 =
                                          let uu____6416 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6416) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6405 in
                                      let cvars =
                                        let uu____6434 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6434
                                          (FStar_List.filter
                                             (fun uu____6448  ->
                                                match uu____6448 with
                                                | (x,uu____6454) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6473 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6473 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6481 =
                                             let uu____6482 =
                                               let uu____6489 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6489) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6482 in
                                           (uu____6481,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6509 =
                                               let uu____6510 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6510 in
                                             varops.mk_unique uu____6509 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6521 =
                                               FStar_Options.log_queries () in
                                             if uu____6521
                                             then
                                               let uu____6524 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6524
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6532 =
                                               let uu____6539 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6539) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6532 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6551 =
                                               let uu____6558 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6558,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6551 in
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
                                             let uu____6579 =
                                               let uu____6586 =
                                                 let uu____6587 =
                                                   let uu____6598 =
                                                     let uu____6599 =
                                                       let uu____6604 =
                                                         let uu____6605 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6605 in
                                                       (f_has_t, uu____6604) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6599 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6598) in
                                                 mkForall_fuel uu____6587 in
                                               (uu____6586,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6579 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6628 =
                                               let uu____6635 =
                                                 let uu____6636 =
                                                   let uu____6647 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6647) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6636 in
                                               (uu____6635,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6628 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6672 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6672);
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
                     let uu____6687 =
                       let uu____6694 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6694,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6687 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6706 =
                       let uu____6713 =
                         let uu____6714 =
                           let uu____6725 =
                             let uu____6726 =
                               let uu____6731 =
                                 let uu____6732 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6732 in
                               (f_has_t, uu____6731) in
                             FStar_SMTEncoding_Util.mkImp uu____6726 in
                           ([[f_has_t]], [fsym], uu____6725) in
                         mkForall_fuel uu____6714 in
                       (uu____6713, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6706 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6759 ->
           let uu____6766 =
             let uu____6771 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6771 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6778;
                 FStar_Syntax_Syntax.vars = uu____6779;_} ->
                 let uu____6786 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6786 with
                  | (b,f1) ->
                      let uu____6811 =
                        let uu____6812 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6812 in
                      (uu____6811, f1))
             | uu____6821 -> failwith "impossible" in
           (match uu____6766 with
            | (x,f) ->
                let uu____6832 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6832 with
                 | (base_t,decls) ->
                     let uu____6843 = gen_term_var env x in
                     (match uu____6843 with
                      | (x1,xtm,env') ->
                          let uu____6857 = encode_formula f env' in
                          (match uu____6857 with
                           | (refinement,decls') ->
                               let uu____6868 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6868 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6884 =
                                        let uu____6887 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6894 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6887
                                          uu____6894 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6884 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6927  ->
                                              match uu____6927 with
                                              | (y,uu____6933) ->
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
                                    let uu____6966 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6966 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6974 =
                                           let uu____6975 =
                                             let uu____6982 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6982) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6975 in
                                         (uu____6974,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____7003 =
                                             let uu____7004 =
                                               let uu____7005 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7005 in
                                             Prims.strcat module_name
                                               uu____7004 in
                                           varops.mk_unique uu____7003 in
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
                                           let uu____7019 =
                                             let uu____7026 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____7026) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7019 in
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
                                           let uu____7041 =
                                             let uu____7048 =
                                               let uu____7049 =
                                                 let uu____7060 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7060) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7049 in
                                             (uu____7048,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7041 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7086 =
                                             let uu____7093 =
                                               let uu____7094 =
                                                 let uu____7105 =
                                                   let uu____7106 =
                                                     let uu____7111 =
                                                       let uu____7112 =
                                                         let uu____7123 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7123) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7112 in
                                                     (uu____7111, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7106 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7105) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7094 in
                                             (uu____7093,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7086 in
                                         let t_kinding =
                                           let uu____7161 =
                                             let uu____7168 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7168,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7161 in
                                         let t_interp =
                                           let uu____7186 =
                                             let uu____7193 =
                                               let uu____7194 =
                                                 let uu____7205 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7205) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7194 in
                                             let uu____7228 =
                                               let uu____7231 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7231 in
                                             (uu____7193, uu____7228,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7186 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7238 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7238);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7268 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7268 in
           let uu____7269 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7269 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7281 =
                    let uu____7288 =
                      let uu____7289 =
                        let uu____7290 =
                          let uu____7291 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7291 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7290 in
                      varops.mk_unique uu____7289 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7288) in
                  FStar_SMTEncoding_Util.mkAssume uu____7281 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7296 ->
           let uu____7311 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7311 with
            | (head1,args_e) ->
                let uu____7352 =
                  let uu____7365 =
                    let uu____7366 = FStar_Syntax_Subst.compress head1 in
                    uu____7366.FStar_Syntax_Syntax.n in
                  (uu____7365, args_e) in
                (match uu____7352 with
                 | uu____7381 when head_redex env head1 ->
                     let uu____7394 = whnf env t in
                     encode_term uu____7394 env
                 | uu____7395 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7414 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7428;
                       FStar_Syntax_Syntax.vars = uu____7429;_},uu____7430),uu____7431::
                    (v1,uu____7433)::(v2,uu____7435)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7486 = encode_term v1 env in
                     (match uu____7486 with
                      | (v11,decls1) ->
                          let uu____7497 = encode_term v2 env in
                          (match uu____7497 with
                           | (v21,decls2) ->
                               let uu____7508 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7508,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7512::(v1,uu____7514)::(v2,uu____7516)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7563 = encode_term v1 env in
                     (match uu____7563 with
                      | (v11,decls1) ->
                          let uu____7574 = encode_term v2 env in
                          (match uu____7574 with
                           | (v21,decls2) ->
                               let uu____7585 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7585,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7588) ->
                     let e0 =
                       let uu____7606 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7606 in
                     ((let uu____7614 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7614
                       then
                         let uu____7615 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7615
                       else ());
                      (let e =
                         let uu____7620 =
                           let uu____7621 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7622 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7621
                             uu____7622 in
                         uu____7620 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7631),(arg,uu____7633)::[]) -> encode_term arg env
                 | uu____7658 ->
                     let uu____7671 = encode_args args_e env in
                     (match uu____7671 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7726 = encode_term head1 env in
                            match uu____7726 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7790 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7790 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7868  ->
                                                 fun uu____7869  ->
                                                   match (uu____7868,
                                                           uu____7869)
                                                   with
                                                   | ((bv,uu____7891),
                                                      (a,uu____7893)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7911 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7911
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7916 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7916 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7931 =
                                                   let uu____7938 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7947 =
                                                     let uu____7948 =
                                                       let uu____7949 =
                                                         let uu____7950 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7950 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7949 in
                                                     varops.mk_unique
                                                       uu____7948 in
                                                   (uu____7938,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7947) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7931 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7967 = lookup_free_var_sym env fv in
                            match uu____7967 with
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
                                   FStar_Syntax_Syntax.pos = uu____7998;
                                   FStar_Syntax_Syntax.vars = uu____7999;_},uu____8000)
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
                                   FStar_Syntax_Syntax.pos = uu____8011;
                                   FStar_Syntax_Syntax.vars = uu____8012;_},uu____8013)
                                ->
                                let uu____8018 =
                                  let uu____8019 =
                                    let uu____8024 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8024
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8019
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8018
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8054 =
                                  let uu____8055 =
                                    let uu____8060 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8060
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8055
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8054
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8089,(FStar_Util.Inl t1,uu____8091),uu____8092)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8141,(FStar_Util.Inr c,uu____8143),uu____8144)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8193 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8220 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8220 in
                               let uu____8221 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8221 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8237;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8238;_},uu____8239)
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
                                     | uu____8253 ->
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
           let uu____8302 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8302 with
            | (bs1,body1,opening) ->
                let fallback uu____8325 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8332 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8332, [decl]) in
                let is_impure rc =
                  let uu____8339 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8339 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8349 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8349
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8369 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8369
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8373 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8373)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8380 =
                         let uu____8381 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8381 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8380);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8383 =
                       (is_impure rc) &&
                         (let uu____8385 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8385) in
                     if uu____8383
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8392 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8392 with
                        | (vars,guards,envbody,decls,uu____8417) ->
                            let body2 =
                              let uu____8431 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8431
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8433 = encode_term body2 envbody in
                            (match uu____8433 with
                             | (body3,decls') ->
                                 let uu____8444 =
                                   let uu____8453 = codomain_eff rc in
                                   match uu____8453 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8472 = encode_term tfun env in
                                       (match uu____8472 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8444 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8504 =
                                          let uu____8515 =
                                            let uu____8516 =
                                              let uu____8521 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8521, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8516 in
                                          ([], vars, uu____8515) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8504 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8533 =
                                              let uu____8536 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8536
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8533 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8555 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8555 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8563 =
                                             let uu____8564 =
                                               let uu____8571 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8571) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8564 in
                                           (uu____8563,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8582 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8582 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8593 =
                                                    let uu____8594 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8594 = cache_size in
                                                  if uu____8593
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
                                                    let uu____8610 =
                                                      let uu____8611 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8611 in
                                                    varops.mk_unique
                                                      uu____8610 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8618 =
                                                    let uu____8625 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8625) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8618 in
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
                                                      let uu____8643 =
                                                        let uu____8644 =
                                                          let uu____8651 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8651,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8644 in
                                                      [uu____8643] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8664 =
                                                    let uu____8671 =
                                                      let uu____8672 =
                                                        let uu____8683 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8683) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8672 in
                                                    (uu____8671,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8664 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8700 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8700);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8703,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8704;
                          FStar_Syntax_Syntax.lbunivs = uu____8705;
                          FStar_Syntax_Syntax.lbtyp = uu____8706;
                          FStar_Syntax_Syntax.lbeff = uu____8707;
                          FStar_Syntax_Syntax.lbdef = uu____8708;_}::uu____8709),uu____8710)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8736;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8738;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8759 ->
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
              let uu____8829 = encode_term e1 env in
              match uu____8829 with
              | (ee1,decls1) ->
                  let uu____8840 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8840 with
                   | (xs,e21) ->
                       let uu____8865 = FStar_List.hd xs in
                       (match uu____8865 with
                        | (x1,uu____8879) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8881 = encode_body e21 env' in
                            (match uu____8881 with
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
            let uu____8913 =
              let uu____8920 =
                let uu____8921 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8921 in
              gen_term_var env uu____8920 in
            match uu____8913 with
            | (scrsym,scr',env1) ->
                let uu____8929 = encode_term e env1 in
                (match uu____8929 with
                 | (scr,decls) ->
                     let uu____8940 =
                       let encode_branch b uu____8965 =
                         match uu____8965 with
                         | (else_case,decls1) ->
                             let uu____8984 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8984 with
                              | (p,w,br) ->
                                  let uu____9010 = encode_pat env1 p in
                                  (match uu____9010 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9047  ->
                                                   match uu____9047 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9054 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9076 =
                                               encode_term w1 env2 in
                                             (match uu____9076 with
                                              | (w2,decls2) ->
                                                  let uu____9089 =
                                                    let uu____9090 =
                                                      let uu____9095 =
                                                        let uu____9096 =
                                                          let uu____9101 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9101) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9096 in
                                                      (guard, uu____9095) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9090 in
                                                  (uu____9089, decls2)) in
                                       (match uu____9054 with
                                        | (guard1,decls2) ->
                                            let uu____9114 =
                                              encode_br br env2 in
                                            (match uu____9114 with
                                             | (br1,decls3) ->
                                                 let uu____9127 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9127,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8940 with
                      | (match_tm,decls1) ->
                          let uu____9146 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9146, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9186 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9186
       then
         let uu____9187 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9187
       else ());
      (let uu____9189 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9189 with
       | (vars,pat_term) ->
           let uu____9206 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9259  ->
                     fun v1  ->
                       match uu____9259 with
                       | (env1,vars1) ->
                           let uu____9311 = gen_term_var env1 v1 in
                           (match uu____9311 with
                            | (xx,uu____9333,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9206 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9412 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9413 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9414 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9422 = encode_const c env1 in
                      (match uu____9422 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9436::uu____9437 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9440 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9463 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9463 with
                        | (uu____9470,uu____9471::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9474 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9507  ->
                                  match uu____9507 with
                                  | (arg,uu____9515) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9521 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9521)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9548) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9579 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9602 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9646  ->
                                  match uu____9646 with
                                  | (arg,uu____9660) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9666 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9666)) in
                      FStar_All.pipe_right uu____9602 FStar_List.flatten in
                let pat_term1 uu____9694 = encode_term pat_term env1 in
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
      let uu____9704 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9742  ->
                fun uu____9743  ->
                  match (uu____9742, uu____9743) with
                  | ((tms,decls),(t,uu____9779)) ->
                      let uu____9800 = encode_term t env in
                      (match uu____9800 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9704 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9857 = FStar_Syntax_Util.list_elements e in
        match uu____9857 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9878 =
          let uu____9893 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9893 FStar_Syntax_Util.head_and_args in
        match uu____9878 with
        | (head1,args) ->
            let uu____9932 =
              let uu____9945 =
                let uu____9946 = FStar_Syntax_Util.un_uinst head1 in
                uu____9946.FStar_Syntax_Syntax.n in
              (uu____9945, args) in
            (match uu____9932 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9960,uu____9961)::(e,uu____9963)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9998 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10034 =
            let uu____10049 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10049 FStar_Syntax_Util.head_and_args in
          match uu____10034 with
          | (head1,args) ->
              let uu____10090 =
                let uu____10103 =
                  let uu____10104 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10104.FStar_Syntax_Syntax.n in
                (uu____10103, args) in
              (match uu____10090 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10121)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10148 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10170 = smt_pat_or1 t1 in
            (match uu____10170 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10186 = list_elements1 e in
                 FStar_All.pipe_right uu____10186
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10204 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10204
                           (FStar_List.map one_pat)))
             | uu____10215 ->
                 let uu____10220 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10220])
        | uu____10241 ->
            let uu____10244 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10244] in
      let uu____10265 =
        let uu____10284 =
          let uu____10285 = FStar_Syntax_Subst.compress t in
          uu____10285.FStar_Syntax_Syntax.n in
        match uu____10284 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10324 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10324 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10367;
                        FStar_Syntax_Syntax.effect_name = uu____10368;
                        FStar_Syntax_Syntax.result_typ = uu____10369;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10371)::(post,uu____10373)::(pats,uu____10375)::[];
                        FStar_Syntax_Syntax.flags = uu____10376;_}
                      ->
                      let uu____10417 = lemma_pats pats in
                      (binders1, pre, post, uu____10417)
                  | uu____10434 -> failwith "impos"))
        | uu____10453 -> failwith "Impos" in
      match uu____10265 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___157_10501 = env in
            {
              bindings = (uu___157_10501.bindings);
              depth = (uu___157_10501.depth);
              tcenv = (uu___157_10501.tcenv);
              warn = (uu___157_10501.warn);
              cache = (uu___157_10501.cache);
              nolabels = (uu___157_10501.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___157_10501.encode_non_total_function_typ);
              current_module_name = (uu___157_10501.current_module_name)
            } in
          let uu____10502 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10502 with
           | (vars,guards,env2,decls,uu____10527) ->
               let uu____10540 =
                 let uu____10553 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10597 =
                             let uu____10606 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10606
                               FStar_List.unzip in
                           match uu____10597 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10553 FStar_List.unzip in
               (match uu____10540 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___158_10715 = env2 in
                      {
                        bindings = (uu___158_10715.bindings);
                        depth = (uu___158_10715.depth);
                        tcenv = (uu___158_10715.tcenv);
                        warn = (uu___158_10715.warn);
                        cache = (uu___158_10715.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___158_10715.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___158_10715.encode_non_total_function_typ);
                        current_module_name =
                          (uu___158_10715.current_module_name)
                      } in
                    let uu____10716 =
                      let uu____10721 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10721 env3 in
                    (match uu____10716 with
                     | (pre1,decls'') ->
                         let uu____10728 =
                           let uu____10733 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10733 env3 in
                         (match uu____10728 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10743 =
                                let uu____10744 =
                                  let uu____10755 =
                                    let uu____10756 =
                                      let uu____10761 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10761, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10756 in
                                  (pats, vars, uu____10755) in
                                FStar_SMTEncoding_Util.mkForall uu____10744 in
                              (uu____10743, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10780 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10780
        then
          let uu____10781 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10782 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10781 uu____10782
        else () in
      let enc f r l =
        let uu____10815 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10843 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10843 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10815 with
        | (decls,args) ->
            let uu____10872 =
              let uu___159_10873 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___159_10873.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___159_10873.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10872, decls) in
      let const_op f r uu____10904 =
        let uu____10917 = f r in (uu____10917, []) in
      let un_op f l =
        let uu____10936 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10936 in
      let bin_op f uu___133_10952 =
        match uu___133_10952 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10963 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10997 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11020  ->
                 match uu____11020 with
                 | (t,uu____11034) ->
                     let uu____11035 = encode_formula t env in
                     (match uu____11035 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10997 with
        | (decls,phis) ->
            let uu____11064 =
              let uu___160_11065 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_11065.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_11065.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11064, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11126  ->
               match uu____11126 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11145) -> false
                    | uu____11146 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11161 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11161
        else
          (let uu____11175 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11175 r rf) in
      let mk_imp1 r uu___134_11200 =
        match uu___134_11200 with
        | (lhs,uu____11206)::(rhs,uu____11208)::[] ->
            let uu____11235 = encode_formula rhs env in
            (match uu____11235 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11250) ->
                      (l1, decls1)
                  | uu____11255 ->
                      let uu____11256 = encode_formula lhs env in
                      (match uu____11256 with
                       | (l2,decls2) ->
                           let uu____11267 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11267, (FStar_List.append decls1 decls2)))))
        | uu____11270 -> failwith "impossible" in
      let mk_ite r uu___135_11291 =
        match uu___135_11291 with
        | (guard,uu____11297)::(_then,uu____11299)::(_else,uu____11301)::[]
            ->
            let uu____11338 = encode_formula guard env in
            (match uu____11338 with
             | (g,decls1) ->
                 let uu____11349 = encode_formula _then env in
                 (match uu____11349 with
                  | (t,decls2) ->
                      let uu____11360 = encode_formula _else env in
                      (match uu____11360 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11374 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11399 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11399 in
      let connectives =
        let uu____11417 =
          let uu____11430 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11430) in
        let uu____11447 =
          let uu____11462 =
            let uu____11475 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11475) in
          let uu____11492 =
            let uu____11507 =
              let uu____11522 =
                let uu____11535 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11535) in
              let uu____11552 =
                let uu____11567 =
                  let uu____11582 =
                    let uu____11595 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11595) in
                  [uu____11582;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11567 in
              uu____11522 :: uu____11552 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11507 in
          uu____11462 :: uu____11492 in
        uu____11417 :: uu____11447 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11916 = encode_formula phi' env in
            (match uu____11916 with
             | (phi2,decls) ->
                 let uu____11927 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11927, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11928 ->
            let uu____11935 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11935 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11974 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11974 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11986;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11988;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12009 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12009 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12056::(x,uu____12058)::(t,uu____12060)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12107 = encode_term x env in
                 (match uu____12107 with
                  | (x1,decls) ->
                      let uu____12118 = encode_term t env in
                      (match uu____12118 with
                       | (t1,decls') ->
                           let uu____12129 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12129, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12134)::(msg,uu____12136)::(phi2,uu____12138)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12183 =
                   let uu____12188 =
                     let uu____12189 = FStar_Syntax_Subst.compress r in
                     uu____12189.FStar_Syntax_Syntax.n in
                   let uu____12192 =
                     let uu____12193 = FStar_Syntax_Subst.compress msg in
                     uu____12193.FStar_Syntax_Syntax.n in
                   (uu____12188, uu____12192) in
                 (match uu____12183 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12202))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12208 -> fallback phi2)
             | uu____12213 when head_redex env head2 ->
                 let uu____12226 = whnf env phi1 in
                 encode_formula uu____12226 env
             | uu____12227 ->
                 let uu____12240 = encode_term phi1 env in
                 (match uu____12240 with
                  | (tt,decls) ->
                      let uu____12251 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___161_12254 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___161_12254.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___161_12254.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12251, decls)))
        | uu____12255 ->
            let uu____12256 = encode_term phi1 env in
            (match uu____12256 with
             | (tt,decls) ->
                 let uu____12267 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___162_12270 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___162_12270.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___162_12270.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12267, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12306 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12306 with
        | (vars,guards,env2,decls,uu____12345) ->
            let uu____12358 =
              let uu____12371 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12419 =
                          let uu____12428 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12458  ->
                                    match uu____12458 with
                                    | (t,uu____12468) ->
                                        encode_term t
                                          (let uu___163_12470 = env2 in
                                           {
                                             bindings =
                                               (uu___163_12470.bindings);
                                             depth = (uu___163_12470.depth);
                                             tcenv = (uu___163_12470.tcenv);
                                             warn = (uu___163_12470.warn);
                                             cache = (uu___163_12470.cache);
                                             nolabels =
                                               (uu___163_12470.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___163_12470.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___163_12470.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12428 FStar_List.unzip in
                        match uu____12419 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12371 FStar_List.unzip in
            (match uu____12358 with
             | (pats,decls') ->
                 let uu____12569 = encode_formula body env2 in
                 (match uu____12569 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12601;
                             FStar_SMTEncoding_Term.rng = uu____12602;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12617 -> guards in
                      let uu____12622 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12622, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12682  ->
                   match uu____12682 with
                   | (x,uu____12688) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12696 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12708 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12708) uu____12696 tl1 in
             let uu____12711 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12738  ->
                       match uu____12738 with
                       | (b,uu____12744) ->
                           let uu____12745 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12745)) in
             (match uu____12711 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12751) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12765 =
                    let uu____12766 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12766 in
                  FStar_Errors.warn pos uu____12765) in
       let uu____12767 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12767 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12776 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12834  ->
                     match uu____12834 with
                     | (l,uu____12848) -> FStar_Ident.lid_equals op l)) in
           (match uu____12776 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12881,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12921 = encode_q_body env vars pats body in
             match uu____12921 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12966 =
                     let uu____12977 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12977) in
                   FStar_SMTEncoding_Term.mkForall uu____12966
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12996 = encode_q_body env vars pats body in
             match uu____12996 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13040 =
                   let uu____13041 =
                     let uu____13052 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13052) in
                   FStar_SMTEncoding_Term.mkExists uu____13041
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13040, decls))))
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
  let uu____13150 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13150 with
  | (asym,a) ->
      let uu____13157 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13157 with
       | (xsym,x) ->
           let uu____13164 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13164 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13208 =
                      let uu____13219 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13219, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13208 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13245 =
                      let uu____13252 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13252) in
                    FStar_SMTEncoding_Util.mkApp uu____13245 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13265 =
                    let uu____13268 =
                      let uu____13271 =
                        let uu____13274 =
                          let uu____13275 =
                            let uu____13282 =
                              let uu____13283 =
                                let uu____13294 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13294) in
                              FStar_SMTEncoding_Util.mkForall uu____13283 in
                            (uu____13282, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13275 in
                        let uu____13311 =
                          let uu____13314 =
                            let uu____13315 =
                              let uu____13322 =
                                let uu____13323 =
                                  let uu____13334 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13334) in
                                FStar_SMTEncoding_Util.mkForall uu____13323 in
                              (uu____13322,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13315 in
                          [uu____13314] in
                        uu____13274 :: uu____13311 in
                      xtok_decl :: uu____13271 in
                    xname_decl :: uu____13268 in
                  (xtok1, uu____13265) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13425 =
                    let uu____13438 =
                      let uu____13447 =
                        let uu____13448 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13448 in
                      quant axy uu____13447 in
                    (FStar_Parser_Const.op_Eq, uu____13438) in
                  let uu____13457 =
                    let uu____13472 =
                      let uu____13485 =
                        let uu____13494 =
                          let uu____13495 =
                            let uu____13496 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13496 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13495 in
                        quant axy uu____13494 in
                      (FStar_Parser_Const.op_notEq, uu____13485) in
                    let uu____13505 =
                      let uu____13520 =
                        let uu____13533 =
                          let uu____13542 =
                            let uu____13543 =
                              let uu____13544 =
                                let uu____13549 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13550 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13549, uu____13550) in
                              FStar_SMTEncoding_Util.mkLT uu____13544 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13543 in
                          quant xy uu____13542 in
                        (FStar_Parser_Const.op_LT, uu____13533) in
                      let uu____13559 =
                        let uu____13574 =
                          let uu____13587 =
                            let uu____13596 =
                              let uu____13597 =
                                let uu____13598 =
                                  let uu____13603 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13604 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13603, uu____13604) in
                                FStar_SMTEncoding_Util.mkLTE uu____13598 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13597 in
                            quant xy uu____13596 in
                          (FStar_Parser_Const.op_LTE, uu____13587) in
                        let uu____13613 =
                          let uu____13628 =
                            let uu____13641 =
                              let uu____13650 =
                                let uu____13651 =
                                  let uu____13652 =
                                    let uu____13657 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13658 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13657, uu____13658) in
                                  FStar_SMTEncoding_Util.mkGT uu____13652 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13651 in
                              quant xy uu____13650 in
                            (FStar_Parser_Const.op_GT, uu____13641) in
                          let uu____13667 =
                            let uu____13682 =
                              let uu____13695 =
                                let uu____13704 =
                                  let uu____13705 =
                                    let uu____13706 =
                                      let uu____13711 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13712 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13711, uu____13712) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13706 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13705 in
                                quant xy uu____13704 in
                              (FStar_Parser_Const.op_GTE, uu____13695) in
                            let uu____13721 =
                              let uu____13736 =
                                let uu____13749 =
                                  let uu____13758 =
                                    let uu____13759 =
                                      let uu____13760 =
                                        let uu____13765 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13766 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13765, uu____13766) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13760 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13759 in
                                  quant xy uu____13758 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13749) in
                              let uu____13775 =
                                let uu____13790 =
                                  let uu____13803 =
                                    let uu____13812 =
                                      let uu____13813 =
                                        let uu____13814 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13814 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13813 in
                                    quant qx uu____13812 in
                                  (FStar_Parser_Const.op_Minus, uu____13803) in
                                let uu____13823 =
                                  let uu____13838 =
                                    let uu____13851 =
                                      let uu____13860 =
                                        let uu____13861 =
                                          let uu____13862 =
                                            let uu____13867 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13868 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13867, uu____13868) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13862 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13861 in
                                      quant xy uu____13860 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13851) in
                                  let uu____13877 =
                                    let uu____13892 =
                                      let uu____13905 =
                                        let uu____13914 =
                                          let uu____13915 =
                                            let uu____13916 =
                                              let uu____13921 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13922 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13921, uu____13922) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13916 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13915 in
                                        quant xy uu____13914 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13905) in
                                    let uu____13931 =
                                      let uu____13946 =
                                        let uu____13959 =
                                          let uu____13968 =
                                            let uu____13969 =
                                              let uu____13970 =
                                                let uu____13975 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13976 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13975, uu____13976) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13970 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13969 in
                                          quant xy uu____13968 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13959) in
                                      let uu____13985 =
                                        let uu____14000 =
                                          let uu____14013 =
                                            let uu____14022 =
                                              let uu____14023 =
                                                let uu____14024 =
                                                  let uu____14029 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14030 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14029, uu____14030) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14024 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14023 in
                                            quant xy uu____14022 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14013) in
                                        let uu____14039 =
                                          let uu____14054 =
                                            let uu____14067 =
                                              let uu____14076 =
                                                let uu____14077 =
                                                  let uu____14078 =
                                                    let uu____14083 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14084 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14083,
                                                      uu____14084) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14078 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14077 in
                                              quant xy uu____14076 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14067) in
                                          let uu____14093 =
                                            let uu____14108 =
                                              let uu____14121 =
                                                let uu____14130 =
                                                  let uu____14131 =
                                                    let uu____14132 =
                                                      let uu____14137 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14138 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14137,
                                                        uu____14138) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14132 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14131 in
                                                quant xy uu____14130 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14121) in
                                            let uu____14147 =
                                              let uu____14162 =
                                                let uu____14175 =
                                                  let uu____14184 =
                                                    let uu____14185 =
                                                      let uu____14186 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14186 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14185 in
                                                  quant qx uu____14184 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14175) in
                                              [uu____14162] in
                                            uu____14108 :: uu____14147 in
                                          uu____14054 :: uu____14093 in
                                        uu____14000 :: uu____14039 in
                                      uu____13946 :: uu____13985 in
                                    uu____13892 :: uu____13931 in
                                  uu____13838 :: uu____13877 in
                                uu____13790 :: uu____13823 in
                              uu____13736 :: uu____13775 in
                            uu____13682 :: uu____13721 in
                          uu____13628 :: uu____13667 in
                        uu____13574 :: uu____13613 in
                      uu____13520 :: uu____13559 in
                    uu____13472 :: uu____13505 in
                  uu____13425 :: uu____13457 in
                let mk1 l v1 =
                  let uu____14400 =
                    let uu____14409 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14467  ->
                              match uu____14467 with
                              | (l',uu____14481) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14409
                      (FStar_Option.map
                         (fun uu____14541  ->
                            match uu____14541 with | (uu____14560,b) -> b v1)) in
                  FStar_All.pipe_right uu____14400 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14631  ->
                          match uu____14631 with
                          | (l',uu____14645) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14686 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14686 with
        | (xxsym,xx) ->
            let uu____14693 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14693 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14703 =
                   let uu____14710 =
                     let uu____14711 =
                       let uu____14722 =
                         let uu____14723 =
                           let uu____14728 =
                             let uu____14729 =
                               let uu____14734 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14734) in
                             FStar_SMTEncoding_Util.mkEq uu____14729 in
                           (xx_has_type, uu____14728) in
                         FStar_SMTEncoding_Util.mkImp uu____14723 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14722) in
                     FStar_SMTEncoding_Util.mkForall uu____14711 in
                   let uu____14759 =
                     let uu____14760 =
                       let uu____14761 =
                         let uu____14762 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14762 in
                       Prims.strcat module_name uu____14761 in
                     varops.mk_unique uu____14760 in
                   (uu____14710, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14759) in
                 FStar_SMTEncoding_Util.mkAssume uu____14703)
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
    let uu____14802 =
      let uu____14803 =
        let uu____14810 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14810, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14803 in
    let uu____14813 =
      let uu____14816 =
        let uu____14817 =
          let uu____14824 =
            let uu____14825 =
              let uu____14836 =
                let uu____14837 =
                  let uu____14842 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14842) in
                FStar_SMTEncoding_Util.mkImp uu____14837 in
              ([[typing_pred]], [xx], uu____14836) in
            mkForall_fuel uu____14825 in
          (uu____14824, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14817 in
      [uu____14816] in
    uu____14802 :: uu____14813 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14884 =
      let uu____14885 =
        let uu____14892 =
          let uu____14893 =
            let uu____14904 =
              let uu____14909 =
                let uu____14912 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14912] in
              [uu____14909] in
            let uu____14917 =
              let uu____14918 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14918 tt in
            (uu____14904, [bb], uu____14917) in
          FStar_SMTEncoding_Util.mkForall uu____14893 in
        (uu____14892, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14885 in
    let uu____14939 =
      let uu____14942 =
        let uu____14943 =
          let uu____14950 =
            let uu____14951 =
              let uu____14962 =
                let uu____14963 =
                  let uu____14968 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14968) in
                FStar_SMTEncoding_Util.mkImp uu____14963 in
              ([[typing_pred]], [xx], uu____14962) in
            mkForall_fuel uu____14951 in
          (uu____14950, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14943 in
      [uu____14942] in
    uu____14884 :: uu____14939 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15018 =
        let uu____15019 =
          let uu____15026 =
            let uu____15029 =
              let uu____15032 =
                let uu____15035 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15036 =
                  let uu____15039 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15039] in
                uu____15035 :: uu____15036 in
              tt :: uu____15032 in
            tt :: uu____15029 in
          ("Prims.Precedes", uu____15026) in
        FStar_SMTEncoding_Util.mkApp uu____15019 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15018 in
    let precedes_y_x =
      let uu____15043 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15043 in
    let uu____15046 =
      let uu____15047 =
        let uu____15054 =
          let uu____15055 =
            let uu____15066 =
              let uu____15071 =
                let uu____15074 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15074] in
              [uu____15071] in
            let uu____15079 =
              let uu____15080 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15080 tt in
            (uu____15066, [bb], uu____15079) in
          FStar_SMTEncoding_Util.mkForall uu____15055 in
        (uu____15054, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15047 in
    let uu____15101 =
      let uu____15104 =
        let uu____15105 =
          let uu____15112 =
            let uu____15113 =
              let uu____15124 =
                let uu____15125 =
                  let uu____15130 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15130) in
                FStar_SMTEncoding_Util.mkImp uu____15125 in
              ([[typing_pred]], [xx], uu____15124) in
            mkForall_fuel uu____15113 in
          (uu____15112, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15105 in
      let uu____15155 =
        let uu____15158 =
          let uu____15159 =
            let uu____15166 =
              let uu____15167 =
                let uu____15178 =
                  let uu____15179 =
                    let uu____15184 =
                      let uu____15185 =
                        let uu____15188 =
                          let uu____15191 =
                            let uu____15194 =
                              let uu____15195 =
                                let uu____15200 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15201 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15200, uu____15201) in
                              FStar_SMTEncoding_Util.mkGT uu____15195 in
                            let uu____15202 =
                              let uu____15205 =
                                let uu____15206 =
                                  let uu____15211 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15212 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15211, uu____15212) in
                                FStar_SMTEncoding_Util.mkGTE uu____15206 in
                              let uu____15213 =
                                let uu____15216 =
                                  let uu____15217 =
                                    let uu____15222 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15223 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15222, uu____15223) in
                                  FStar_SMTEncoding_Util.mkLT uu____15217 in
                                [uu____15216] in
                              uu____15205 :: uu____15213 in
                            uu____15194 :: uu____15202 in
                          typing_pred_y :: uu____15191 in
                        typing_pred :: uu____15188 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15185 in
                    (uu____15184, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15179 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15178) in
              mkForall_fuel uu____15167 in
            (uu____15166,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15159 in
        [uu____15158] in
      uu____15104 :: uu____15155 in
    uu____15046 :: uu____15101 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15269 =
      let uu____15270 =
        let uu____15277 =
          let uu____15278 =
            let uu____15289 =
              let uu____15294 =
                let uu____15297 = FStar_SMTEncoding_Term.boxString b in
                [uu____15297] in
              [uu____15294] in
            let uu____15302 =
              let uu____15303 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15303 tt in
            (uu____15289, [bb], uu____15302) in
          FStar_SMTEncoding_Util.mkForall uu____15278 in
        (uu____15277, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15270 in
    let uu____15324 =
      let uu____15327 =
        let uu____15328 =
          let uu____15335 =
            let uu____15336 =
              let uu____15347 =
                let uu____15348 =
                  let uu____15353 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15353) in
                FStar_SMTEncoding_Util.mkImp uu____15348 in
              ([[typing_pred]], [xx], uu____15347) in
            mkForall_fuel uu____15336 in
          (uu____15335, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15328 in
      [uu____15327] in
    uu____15269 :: uu____15324 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15406 =
      let uu____15407 =
        let uu____15414 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15414, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15407 in
    [uu____15406] in
  let mk_and_interp env conj uu____15426 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15451 =
      let uu____15452 =
        let uu____15459 =
          let uu____15460 =
            let uu____15471 =
              let uu____15472 =
                let uu____15477 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15477, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15472 in
            ([[l_and_a_b]], [aa; bb], uu____15471) in
          FStar_SMTEncoding_Util.mkForall uu____15460 in
        (uu____15459, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15452 in
    [uu____15451] in
  let mk_or_interp env disj uu____15515 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15540 =
      let uu____15541 =
        let uu____15548 =
          let uu____15549 =
            let uu____15560 =
              let uu____15561 =
                let uu____15566 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15566, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15561 in
            ([[l_or_a_b]], [aa; bb], uu____15560) in
          FStar_SMTEncoding_Util.mkForall uu____15549 in
        (uu____15548, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15541 in
    [uu____15540] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15629 =
      let uu____15630 =
        let uu____15637 =
          let uu____15638 =
            let uu____15649 =
              let uu____15650 =
                let uu____15655 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15655, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15650 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15649) in
          FStar_SMTEncoding_Util.mkForall uu____15638 in
        (uu____15637, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15630 in
    [uu____15629] in
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
    let uu____15728 =
      let uu____15729 =
        let uu____15736 =
          let uu____15737 =
            let uu____15748 =
              let uu____15749 =
                let uu____15754 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15754, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15749 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15748) in
          FStar_SMTEncoding_Util.mkForall uu____15737 in
        (uu____15736, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15729 in
    [uu____15728] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15825 =
      let uu____15826 =
        let uu____15833 =
          let uu____15834 =
            let uu____15845 =
              let uu____15846 =
                let uu____15851 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15851, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15846 in
            ([[l_imp_a_b]], [aa; bb], uu____15845) in
          FStar_SMTEncoding_Util.mkForall uu____15834 in
        (uu____15833, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15826 in
    [uu____15825] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15914 =
      let uu____15915 =
        let uu____15922 =
          let uu____15923 =
            let uu____15934 =
              let uu____15935 =
                let uu____15940 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15940, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15935 in
            ([[l_iff_a_b]], [aa; bb], uu____15934) in
          FStar_SMTEncoding_Util.mkForall uu____15923 in
        (uu____15922, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15915 in
    [uu____15914] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15992 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15992 in
    let uu____15995 =
      let uu____15996 =
        let uu____16003 =
          let uu____16004 =
            let uu____16015 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16015) in
          FStar_SMTEncoding_Util.mkForall uu____16004 in
        (uu____16003, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15996 in
    [uu____15995] in
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
      let uu____16075 =
        let uu____16082 =
          let uu____16085 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16085] in
        ("Valid", uu____16082) in
      FStar_SMTEncoding_Util.mkApp uu____16075 in
    let uu____16088 =
      let uu____16089 =
        let uu____16096 =
          let uu____16097 =
            let uu____16108 =
              let uu____16109 =
                let uu____16114 =
                  let uu____16115 =
                    let uu____16126 =
                      let uu____16131 =
                        let uu____16134 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16134] in
                      [uu____16131] in
                    let uu____16139 =
                      let uu____16140 =
                        let uu____16145 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16145, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16140 in
                    (uu____16126, [xx1], uu____16139) in
                  FStar_SMTEncoding_Util.mkForall uu____16115 in
                (uu____16114, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16109 in
            ([[l_forall_a_b]], [aa; bb], uu____16108) in
          FStar_SMTEncoding_Util.mkForall uu____16097 in
        (uu____16096, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16089 in
    [uu____16088] in
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
      let uu____16227 =
        let uu____16234 =
          let uu____16237 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16237] in
        ("Valid", uu____16234) in
      FStar_SMTEncoding_Util.mkApp uu____16227 in
    let uu____16240 =
      let uu____16241 =
        let uu____16248 =
          let uu____16249 =
            let uu____16260 =
              let uu____16261 =
                let uu____16266 =
                  let uu____16267 =
                    let uu____16278 =
                      let uu____16283 =
                        let uu____16286 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16286] in
                      [uu____16283] in
                    let uu____16291 =
                      let uu____16292 =
                        let uu____16297 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16297, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16292 in
                    (uu____16278, [xx1], uu____16291) in
                  FStar_SMTEncoding_Util.mkExists uu____16267 in
                (uu____16266, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16261 in
            ([[l_exists_a_b]], [aa; bb], uu____16260) in
          FStar_SMTEncoding_Util.mkForall uu____16249 in
        (uu____16248, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16241 in
    [uu____16240] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16357 =
      let uu____16358 =
        let uu____16365 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16366 = varops.mk_unique "typing_range_const" in
        (uu____16365, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16366) in
      FStar_SMTEncoding_Util.mkAssume uu____16358 in
    [uu____16357] in
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
        let uu____16400 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16400 x1 t in
      let uu____16401 =
        let uu____16412 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16412) in
      FStar_SMTEncoding_Util.mkForall uu____16401 in
    let uu____16435 =
      let uu____16436 =
        let uu____16443 =
          let uu____16444 =
            let uu____16455 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16455) in
          FStar_SMTEncoding_Util.mkForall uu____16444 in
        (uu____16443,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16436 in
    [uu____16435] in
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
          let uu____16779 =
            FStar_Util.find_opt
              (fun uu____16805  ->
                 match uu____16805 with
                 | (l,uu____16817) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16779 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16842,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16881 = encode_function_type_as_formula t env in
        match uu____16881 with
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
              let uu____16927 =
                ((let uu____16930 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16930) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16927
              then
                let uu____16937 = new_term_constant_and_tok_from_lid env lid in
                match uu____16937 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16956 =
                        let uu____16957 = FStar_Syntax_Subst.compress t_norm in
                        uu____16957.FStar_Syntax_Syntax.n in
                      match uu____16956 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16963) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16993  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16998 -> [] in
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
                (let uu____17012 = prims.is lid in
                 if uu____17012
                 then
                   let vname = varops.new_fvar lid in
                   let uu____17020 = prims.mk lid vname in
                   match uu____17020 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17044 =
                      let uu____17055 = curried_arrow_formals_comp t_norm in
                      match uu____17055 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17073 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17073
                            then
                              let uu____17074 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___164_17077 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___164_17077.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___164_17077.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___164_17077.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___164_17077.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___164_17077.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___164_17077.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___164_17077.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___164_17077.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___164_17077.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___164_17077.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___164_17077.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___164_17077.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___164_17077.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___164_17077.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___164_17077.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___164_17077.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___164_17077.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___164_17077.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___164_17077.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___164_17077.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___164_17077.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___164_17077.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___164_17077.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___164_17077.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___164_17077.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___164_17077.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___164_17077.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___164_17077.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___164_17077.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___164_17077.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___164_17077.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___164_17077.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17074
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17089 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17089)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17044 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17134 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17134 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17155 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___136_17197  ->
                                       match uu___136_17197 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17201 =
                                             FStar_Util.prefix vars in
                                           (match uu____17201 with
                                            | (uu____17222,(xxsym,uu____17224))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17242 =
                                                  let uu____17243 =
                                                    let uu____17250 =
                                                      let uu____17251 =
                                                        let uu____17262 =
                                                          let uu____17263 =
                                                            let uu____17268 =
                                                              let uu____17269
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17269 in
                                                            (vapp,
                                                              uu____17268) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17263 in
                                                        ([[vapp]], vars,
                                                          uu____17262) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17251 in
                                                    (uu____17250,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17243 in
                                                [uu____17242])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17288 =
                                             FStar_Util.prefix vars in
                                           (match uu____17288 with
                                            | (uu____17309,(xxsym,uu____17311))
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
                                                let uu____17334 =
                                                  let uu____17335 =
                                                    let uu____17342 =
                                                      let uu____17343 =
                                                        let uu____17354 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17354) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17343 in
                                                    (uu____17342,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17335 in
                                                [uu____17334])
                                       | uu____17371 -> [])) in
                             let uu____17372 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17372 with
                              | (vars,guards,env',decls1,uu____17399) ->
                                  let uu____17412 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17421 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17421, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17423 =
                                          encode_formula p env' in
                                        (match uu____17423 with
                                         | (g,ds) ->
                                             let uu____17434 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17434,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17412 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17447 =
                                           let uu____17454 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17454) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17447 in
                                       let uu____17463 =
                                         let vname_decl =
                                           let uu____17471 =
                                             let uu____17482 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17492  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17482,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17471 in
                                         let uu____17501 =
                                           let env2 =
                                             let uu___165_17507 = env1 in
                                             {
                                               bindings =
                                                 (uu___165_17507.bindings);
                                               depth = (uu___165_17507.depth);
                                               tcenv = (uu___165_17507.tcenv);
                                               warn = (uu___165_17507.warn);
                                               cache = (uu___165_17507.cache);
                                               nolabels =
                                                 (uu___165_17507.nolabels);
                                               use_zfuel_name =
                                                 (uu___165_17507.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___165_17507.current_module_name)
                                             } in
                                           let uu____17508 =
                                             let uu____17509 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17509 in
                                           if uu____17508
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17501 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17524::uu____17525 ->
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
                                                     let uu____17565 =
                                                       let uu____17576 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17576) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17565 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17603 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17606 =
                                               match formals with
                                               | [] ->
                                                   let uu____17623 =
                                                     let uu____17624 =
                                                       let uu____17627 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17627 in
                                                     push_free_var env1 lid
                                                       vname uu____17624 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17623)
                                               | uu____17632 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17639 =
                                                       let uu____17646 =
                                                         let uu____17647 =
                                                           let uu____17658 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17658) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17647 in
                                                       (uu____17646,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17639 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17606 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17463 with
                                        | (decls2,env2) ->
                                            let uu____17701 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17709 =
                                                encode_term res_t1 env' in
                                              match uu____17709 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17722 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17722, decls) in
                                            (match uu____17701 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17733 =
                                                     let uu____17740 =
                                                       let uu____17741 =
                                                         let uu____17752 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17752) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17741 in
                                                     (uu____17740,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17733 in
                                                 let freshness =
                                                   let uu____17768 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17768
                                                   then
                                                     let uu____17773 =
                                                       let uu____17774 =
                                                         let uu____17785 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17796 =
                                                           varops.next_id () in
                                                         (vname, uu____17785,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17796) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17774 in
                                                     let uu____17799 =
                                                       let uu____17802 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17802] in
                                                     uu____17773 ::
                                                       uu____17799
                                                   else [] in
                                                 let g =
                                                   let uu____17807 =
                                                     let uu____17810 =
                                                       let uu____17813 =
                                                         let uu____17816 =
                                                           let uu____17819 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17819 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17816 in
                                                       FStar_List.append
                                                         decls3 uu____17813 in
                                                     FStar_List.append decls2
                                                       uu____17810 in
                                                   FStar_List.append decls11
                                                     uu____17807 in
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
          let uu____17854 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17854 with
          | FStar_Pervasives_Native.None  ->
              let uu____17891 = encode_free_var false env x t t_norm [] in
              (match uu____17891 with
               | (decls,env1) ->
                   let uu____17918 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17918 with
                    | (n1,x',uu____17945) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17966) ->
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
            let uu____18026 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____18026 with
            | (decls,env1) ->
                let uu____18045 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18045
                then
                  let uu____18052 =
                    let uu____18055 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18055 in
                  (uu____18052, env1)
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
             (fun uu____18110  ->
                fun lb  ->
                  match uu____18110 with
                  | (decls,env1) ->
                      let uu____18130 =
                        let uu____18137 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18137
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18130 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18159 = FStar_Syntax_Util.head_and_args t in
    match uu____18159 with
    | (hd1,args) ->
        let uu____18196 =
          let uu____18197 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18197.FStar_Syntax_Syntax.n in
        (match uu____18196 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18201,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18220 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18245  ->
      fun quals  ->
        match uu____18245 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18321 = FStar_Util.first_N nbinders formals in
              match uu____18321 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18402  ->
                         fun uu____18403  ->
                           match (uu____18402, uu____18403) with
                           | ((formal,uu____18421),(binder,uu____18423)) ->
                               let uu____18432 =
                                 let uu____18439 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18439) in
                               FStar_Syntax_Syntax.NT uu____18432) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18447 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18478  ->
                              match uu____18478 with
                              | (x,i) ->
                                  let uu____18489 =
                                    let uu___166_18490 = x in
                                    let uu____18491 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___166_18490.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___166_18490.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18491
                                    } in
                                  (uu____18489, i))) in
                    FStar_All.pipe_right uu____18447
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18509 =
                      let uu____18510 = FStar_Syntax_Subst.compress body in
                      let uu____18511 =
                        let uu____18512 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18512 in
                      FStar_Syntax_Syntax.extend_app_n uu____18510
                        uu____18511 in
                    uu____18509 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18573 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18573
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___167_18576 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___167_18576.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___167_18576.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___167_18576.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___167_18576.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___167_18576.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___167_18576.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___167_18576.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___167_18576.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___167_18576.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___167_18576.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___167_18576.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___167_18576.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___167_18576.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___167_18576.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___167_18576.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___167_18576.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___167_18576.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___167_18576.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___167_18576.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___167_18576.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___167_18576.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___167_18576.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___167_18576.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___167_18576.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___167_18576.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___167_18576.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___167_18576.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___167_18576.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___167_18576.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___167_18576.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___167_18576.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___167_18576.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18609 = FStar_Syntax_Util.abs_formals e in
                match uu____18609 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18673::uu____18674 ->
                         let uu____18689 =
                           let uu____18690 =
                             let uu____18693 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18693 in
                           uu____18690.FStar_Syntax_Syntax.n in
                         (match uu____18689 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18736 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18736 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18778 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18778
                                   then
                                     let uu____18813 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18813 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18907  ->
                                                   fun uu____18908  ->
                                                     match (uu____18907,
                                                             uu____18908)
                                                     with
                                                     | ((x,uu____18926),
                                                        (b,uu____18928)) ->
                                                         let uu____18937 =
                                                           let uu____18944 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18944) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18937)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18946 =
                                            let uu____18967 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18967) in
                                          (uu____18946, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19035 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19035 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19124) ->
                              let uu____19129 =
                                let uu____19150 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19150 in
                              (uu____19129, true)
                          | uu____19215 when Prims.op_Negation norm1 ->
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
                          | uu____19217 ->
                              let uu____19218 =
                                let uu____19219 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19220 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19219
                                  uu____19220 in
                              failwith uu____19218)
                     | uu____19245 ->
                         let uu____19246 =
                           let uu____19247 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19247.FStar_Syntax_Syntax.n in
                         (match uu____19246 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19292 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19292 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19324 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19324 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19407 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19463 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19463
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19475 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19569  ->
                            fun lb  ->
                              match uu____19569 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19664 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19664
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19667 =
                                      let uu____19682 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19682
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19667 with
                                    | (tok,decl,env2) ->
                                        let uu____19728 =
                                          let uu____19741 =
                                            let uu____19752 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19752, tok) in
                                          uu____19741 :: toks in
                                        (uu____19728, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19475 with
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
                        | uu____19935 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19943 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19943 vars)
                            else
                              (let uu____19945 =
                                 let uu____19952 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19952) in
                               FStar_SMTEncoding_Util.mkApp uu____19945) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20034;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20036;
                             FStar_Syntax_Syntax.lbeff = uu____20037;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20100 =
                              let uu____20107 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20107 with
                              | (tcenv',uu____20125,e_t) ->
                                  let uu____20131 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20142 -> failwith "Impossible" in
                                  (match uu____20131 with
                                   | (e1,t_norm1) ->
                                       ((let uu___170_20158 = env2 in
                                         {
                                           bindings =
                                             (uu___170_20158.bindings);
                                           depth = (uu___170_20158.depth);
                                           tcenv = tcenv';
                                           warn = (uu___170_20158.warn);
                                           cache = (uu___170_20158.cache);
                                           nolabels =
                                             (uu___170_20158.nolabels);
                                           use_zfuel_name =
                                             (uu___170_20158.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___170_20158.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___170_20158.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20100 with
                             | (env',e1,t_norm1) ->
                                 let uu____20168 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20168 with
                                  | ((binders,body,uu____20189,uu____20190),curry)
                                      ->
                                      ((let uu____20201 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20201
                                        then
                                          let uu____20202 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20203 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20202 uu____20203
                                        else ());
                                       (let uu____20205 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20205 with
                                        | (vars,guards,env'1,binder_decls,uu____20232)
                                            ->
                                            let body1 =
                                              let uu____20246 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20246
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20249 =
                                              let uu____20258 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20258
                                              then
                                                let uu____20269 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20270 =
                                                  encode_formula body1 env'1 in
                                                (uu____20269, uu____20270)
                                              else
                                                (let uu____20280 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20280)) in
                                            (match uu____20249 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20303 =
                                                     let uu____20310 =
                                                       let uu____20311 =
                                                         let uu____20322 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20322) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20311 in
                                                     let uu____20333 =
                                                       let uu____20336 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20336 in
                                                     (uu____20310,
                                                       uu____20333,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20303 in
                                                 let uu____20339 =
                                                   let uu____20342 =
                                                     let uu____20345 =
                                                       let uu____20348 =
                                                         let uu____20351 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20351 in
                                                       FStar_List.append
                                                         decls2 uu____20348 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20345 in
                                                   FStar_List.append decls1
                                                     uu____20342 in
                                                 (uu____20339, env2))))))
                        | uu____20356 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20441 = varops.fresh "fuel" in
                          (uu____20441, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20444 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20532  ->
                                  fun uu____20533  ->
                                    match (uu____20532, uu____20533) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20681 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20681 in
                                        let gtok =
                                          let uu____20683 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20683 in
                                        let env4 =
                                          let uu____20685 =
                                            let uu____20688 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20688 in
                                          push_free_var env3 flid gtok
                                            uu____20685 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20444 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20844 t_norm
                              uu____20846 =
                              match (uu____20844, uu____20846) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20890;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20891;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20919 =
                                    let uu____20926 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20926 with
                                    | (tcenv',uu____20948,e_t) ->
                                        let uu____20954 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20965 ->
                                              failwith "Impossible" in
                                        (match uu____20954 with
                                         | (e1,t_norm1) ->
                                             ((let uu___171_20981 = env3 in
                                               {
                                                 bindings =
                                                   (uu___171_20981.bindings);
                                                 depth =
                                                   (uu___171_20981.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___171_20981.warn);
                                                 cache =
                                                   (uu___171_20981.cache);
                                                 nolabels =
                                                   (uu___171_20981.nolabels);
                                                 use_zfuel_name =
                                                   (uu___171_20981.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___171_20981.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___171_20981.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20919 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20996 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20996
                                         then
                                           let uu____20997 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20998 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20999 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20997 uu____20998
                                             uu____20999
                                         else ());
                                        (let uu____21001 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____21001 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21038 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____21038
                                               then
                                                 let uu____21039 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____21040 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____21041 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21042 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21039 uu____21040
                                                   uu____21041 uu____21042
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21046 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21046 with
                                               | (vars,guards,env'1,binder_decls,uu____21077)
                                                   ->
                                                   let decl_g =
                                                     let uu____21091 =
                                                       let uu____21102 =
                                                         let uu____21105 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21105 in
                                                       (g, uu____21102,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21091 in
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
                                                     let uu____21130 =
                                                       let uu____21137 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21137) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21130 in
                                                   let gsapp =
                                                     let uu____21147 =
                                                       let uu____21154 =
                                                         let uu____21157 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21157 ::
                                                           vars_tm in
                                                       (g, uu____21154) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21147 in
                                                   let gmax =
                                                     let uu____21163 =
                                                       let uu____21170 =
                                                         let uu____21173 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21173 ::
                                                           vars_tm in
                                                       (g, uu____21170) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21163 in
                                                   let body1 =
                                                     let uu____21179 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21179
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21181 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21181 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21199 =
                                                            let uu____21206 =
                                                              let uu____21207
                                                                =
                                                                let uu____21222
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
                                                                  uu____21222) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21207 in
                                                            let uu____21243 =
                                                              let uu____21246
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21246 in
                                                            (uu____21206,
                                                              uu____21243,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21199 in
                                                        let eqn_f =
                                                          let uu____21250 =
                                                            let uu____21257 =
                                                              let uu____21258
                                                                =
                                                                let uu____21269
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21269) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21258 in
                                                            (uu____21257,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21250 in
                                                        let eqn_g' =
                                                          let uu____21283 =
                                                            let uu____21290 =
                                                              let uu____21291
                                                                =
                                                                let uu____21302
                                                                  =
                                                                  let uu____21303
                                                                    =
                                                                    let uu____21308
                                                                    =
                                                                    let uu____21309
                                                                    =
                                                                    let uu____21316
                                                                    =
                                                                    let uu____21319
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21319
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21316) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21309 in
                                                                    (gsapp,
                                                                    uu____21308) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21303 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21302) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21291 in
                                                            (uu____21290,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21283 in
                                                        let uu____21342 =
                                                          let uu____21351 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21351
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21380)
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
                                                                  let uu____21405
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21405
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21410
                                                                  =
                                                                  let uu____21417
                                                                    =
                                                                    let uu____21418
                                                                    =
                                                                    let uu____21429
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21429) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21418 in
                                                                  (uu____21417,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21410 in
                                                              let uu____21450
                                                                =
                                                                let uu____21457
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21457
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21470
                                                                    =
                                                                    let uu____21473
                                                                    =
                                                                    let uu____21474
                                                                    =
                                                                    let uu____21481
                                                                    =
                                                                    let uu____21482
                                                                    =
                                                                    let uu____21493
                                                                    =
                                                                    let uu____21494
                                                                    =
                                                                    let uu____21499
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21499,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21494 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21493) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21482 in
                                                                    (uu____21481,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21474 in
                                                                    [uu____21473] in
                                                                    (d3,
                                                                    uu____21470) in
                                                              (match uu____21450
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21342
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
                            let uu____21564 =
                              let uu____21577 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21656  ->
                                   fun uu____21657  ->
                                     match (uu____21656, uu____21657) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21812 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21812 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21577 in
                            (match uu____21564 with
                             | (decls2,eqns,env01) ->
                                 let uu____21885 =
                                   let isDeclFun uu___137_21897 =
                                     match uu___137_21897 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21898 -> true
                                     | uu____21909 -> false in
                                   let uu____21910 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21910
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21885 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21950 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___138_21954  ->
                                 match uu___138_21954 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21955 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21961 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21961))) in
                      if uu____21950
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
                   let uu____22013 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22013
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
        let uu____22062 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22062 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22066 = encode_sigelt' env se in
      match uu____22066 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22082 =
                  let uu____22083 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22083 in
                [uu____22082]
            | uu____22084 ->
                let uu____22085 =
                  let uu____22088 =
                    let uu____22089 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22089 in
                  uu____22088 :: g in
                let uu____22090 =
                  let uu____22093 =
                    let uu____22094 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22094 in
                  [uu____22093] in
                FStar_List.append uu____22085 uu____22090 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22107 =
          let uu____22108 = FStar_Syntax_Subst.compress t in
          uu____22108.FStar_Syntax_Syntax.n in
        match uu____22107 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22112)) -> s = "opaque_to_smt"
        | uu____22113 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22118 =
          let uu____22119 = FStar_Syntax_Subst.compress t in
          uu____22119.FStar_Syntax_Syntax.n in
        match uu____22118 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22123)) -> s = "uninterpreted_by_smt"
        | uu____22124 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22129 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22134 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22137 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22140 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22155 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22159 =
            let uu____22160 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22160 Prims.op_Negation in
          if uu____22159
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22186 ->
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
               let uu____22206 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22206 with
               | (aname,atok,env2) ->
                   let uu____22222 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22222 with
                    | (formals,uu____22240) ->
                        let uu____22253 =
                          let uu____22258 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22258 env2 in
                        (match uu____22253 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22270 =
                                 let uu____22271 =
                                   let uu____22282 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22298  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22282,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22271 in
                               [uu____22270;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22311 =
                               let aux uu____22363 uu____22364 =
                                 match (uu____22363, uu____22364) with
                                 | ((bv,uu____22416),(env3,acc_sorts,acc)) ->
                                     let uu____22454 = gen_term_var env3 bv in
                                     (match uu____22454 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22311 with
                              | (uu____22526,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22549 =
                                      let uu____22556 =
                                        let uu____22557 =
                                          let uu____22568 =
                                            let uu____22569 =
                                              let uu____22574 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22574) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22569 in
                                          ([[app]], xs_sorts, uu____22568) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22557 in
                                      (uu____22556,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22549 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22594 =
                                      let uu____22601 =
                                        let uu____22602 =
                                          let uu____22613 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22613) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22602 in
                                      (uu____22601,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22594 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22632 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22632 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22660,uu____22661)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22662 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22662 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22679,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22685 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___139_22689  ->
                      match uu___139_22689 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22690 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22695 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22696 -> false)) in
            Prims.op_Negation uu____22685 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22705 =
               let uu____22712 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22712 env fv t quals in
             match uu____22705 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22727 =
                   let uu____22730 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22730 in
                 (uu____22727, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22738 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22738 with
           | (uu____22747,f1) ->
               let uu____22749 = encode_formula f1 env in
               (match uu____22749 with
                | (f2,decls) ->
                    let g =
                      let uu____22763 =
                        let uu____22764 =
                          let uu____22771 =
                            let uu____22774 =
                              let uu____22775 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22775 in
                            FStar_Pervasives_Native.Some uu____22774 in
                          let uu____22776 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22771, uu____22776) in
                        FStar_SMTEncoding_Util.mkAssume uu____22764 in
                      [uu____22763] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22782) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22794 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22812 =
                       let uu____22815 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22815.FStar_Syntax_Syntax.fv_name in
                     uu____22812.FStar_Syntax_Syntax.v in
                   let uu____22816 =
                     let uu____22817 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22817 in
                   if uu____22816
                   then
                     let val_decl =
                       let uu___174_22845 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___174_22845.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___174_22845.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___174_22845.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22850 = encode_sigelt' env1 val_decl in
                     match uu____22850 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22794 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22878,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22880;
                          FStar_Syntax_Syntax.lbtyp = uu____22881;
                          FStar_Syntax_Syntax.lbeff = uu____22882;
                          FStar_Syntax_Syntax.lbdef = uu____22883;_}::[]),uu____22884)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22903 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22903 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22932 =
                   let uu____22935 =
                     let uu____22936 =
                       let uu____22943 =
                         let uu____22944 =
                           let uu____22955 =
                             let uu____22956 =
                               let uu____22961 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22961) in
                             FStar_SMTEncoding_Util.mkEq uu____22956 in
                           ([[b2t_x]], [xx], uu____22955) in
                         FStar_SMTEncoding_Util.mkForall uu____22944 in
                       (uu____22943,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22936 in
                   [uu____22935] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22932 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22994,uu____22995) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___140_23004  ->
                  match uu___140_23004 with
                  | FStar_Syntax_Syntax.Discriminator uu____23005 -> true
                  | uu____23006 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23009,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23020 =
                     let uu____23021 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23021.FStar_Ident.idText in
                   uu____23020 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___141_23025  ->
                     match uu___141_23025 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23026 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23030) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___142_23047  ->
                  match uu___142_23047 with
                  | FStar_Syntax_Syntax.Projector uu____23048 -> true
                  | uu____23053 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23056 = try_lookup_free_var env l in
          (match uu____23056 with
           | FStar_Pervasives_Native.Some uu____23063 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___175_23067 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___175_23067.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___175_23067.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___175_23067.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23074) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23092) ->
          let uu____23101 = encode_sigelts env ses in
          (match uu____23101 with
           | (g,env1) ->
               let uu____23118 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___143_23141  ->
                         match uu___143_23141 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23142;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23143;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23144;_}
                             -> false
                         | uu____23147 -> true)) in
               (match uu____23118 with
                | (g',inversions) ->
                    let uu____23162 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___144_23183  ->
                              match uu___144_23183 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23184 ->
                                  true
                              | uu____23195 -> false)) in
                    (match uu____23162 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23213,tps,k,uu____23216,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___145_23233  ->
                    match uu___145_23233 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23234 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23243 = c in
              match uu____23243 with
              | (name,args,uu____23248,uu____23249,uu____23250) ->
                  let uu____23255 =
                    let uu____23256 =
                      let uu____23267 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23284  ->
                                match uu____23284 with
                                | (uu____23291,sort,uu____23293) -> sort)) in
                      (name, uu____23267, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23256 in
                  [uu____23255]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23320 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23326 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23326 FStar_Option.isNone)) in
            if uu____23320
            then []
            else
              (let uu____23358 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23358 with
               | (xxsym,xx) ->
                   let uu____23367 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23406  ->
                             fun l  ->
                               match uu____23406 with
                               | (out,decls) ->
                                   let uu____23426 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23426 with
                                    | (uu____23437,data_t) ->
                                        let uu____23439 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23439 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23485 =
                                                 let uu____23486 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23486.FStar_Syntax_Syntax.n in
                                               match uu____23485 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23497,indices) ->
                                                   indices
                                               | uu____23519 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23543  ->
                                                         match uu____23543
                                                         with
                                                         | (x,uu____23549) ->
                                                             let uu____23550
                                                               =
                                                               let uu____23551
                                                                 =
                                                                 let uu____23558
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23558,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23551 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23550)
                                                    env) in
                                             let uu____23561 =
                                               encode_args indices env1 in
                                             (match uu____23561 with
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
                                                      let uu____23587 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23603
                                                                 =
                                                                 let uu____23608
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23608,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23603)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23587
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23611 =
                                                      let uu____23612 =
                                                        let uu____23617 =
                                                          let uu____23618 =
                                                            let uu____23623 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23623,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23618 in
                                                        (out, uu____23617) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23612 in
                                                    (uu____23611,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23367 with
                    | (data_ax,decls) ->
                        let uu____23636 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23636 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23647 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23647 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23651 =
                                 let uu____23658 =
                                   let uu____23659 =
                                     let uu____23670 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23685 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23670,
                                       uu____23685) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23659 in
                                 let uu____23700 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23658,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23700) in
                               FStar_SMTEncoding_Util.mkAssume uu____23651 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23703 =
            let uu____23716 =
              let uu____23717 = FStar_Syntax_Subst.compress k in
              uu____23717.FStar_Syntax_Syntax.n in
            match uu____23716 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23762 -> (tps, k) in
          (match uu____23703 with
           | (formals,res) ->
               let uu____23785 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23785 with
                | (formals1,res1) ->
                    let uu____23796 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23796 with
                     | (vars,guards,env',binder_decls,uu____23821) ->
                         let uu____23834 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23834 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23853 =
                                  let uu____23860 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23860) in
                                FStar_SMTEncoding_Util.mkApp uu____23853 in
                              let uu____23869 =
                                let tname_decl =
                                  let uu____23879 =
                                    let uu____23880 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23912  ->
                                              match uu____23912 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23925 = varops.next_id () in
                                    (tname, uu____23880,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23925, false) in
                                  constructor_or_logic_type_decl uu____23879 in
                                let uu____23934 =
                                  match vars with
                                  | [] ->
                                      let uu____23947 =
                                        let uu____23948 =
                                          let uu____23951 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23951 in
                                        push_free_var env1 t tname
                                          uu____23948 in
                                      ([], uu____23947)
                                  | uu____23958 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23967 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23967 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23981 =
                                          let uu____23988 =
                                            let uu____23989 =
                                              let uu____24004 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24004) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23989 in
                                          (uu____23988,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23981 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23934 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23869 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24044 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24044 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24062 =
                                               let uu____24063 =
                                                 let uu____24070 =
                                                   let uu____24071 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24071 in
                                                 (uu____24070,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24063 in
                                             [uu____24062]
                                           else [] in
                                         let uu____24075 =
                                           let uu____24078 =
                                             let uu____24081 =
                                               let uu____24082 =
                                                 let uu____24089 =
                                                   let uu____24090 =
                                                     let uu____24101 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24101) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24090 in
                                                 (uu____24089,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24082 in
                                             [uu____24081] in
                                           FStar_List.append karr uu____24078 in
                                         FStar_List.append decls1 uu____24075 in
                                   let aux =
                                     let uu____24117 =
                                       let uu____24120 =
                                         inversion_axioms tapp vars in
                                       let uu____24123 =
                                         let uu____24126 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24126] in
                                       FStar_List.append uu____24120
                                         uu____24123 in
                                     FStar_List.append kindingAx uu____24117 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24133,uu____24134,uu____24135,uu____24136,uu____24137)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24145,t,uu____24147,n_tps,uu____24149) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24157 = new_term_constant_and_tok_from_lid env d in
          (match uu____24157 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24174 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24174 with
                | (formals,t_res) ->
                    let uu____24209 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24209 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24223 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24223 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24293 =
                                            mk_term_projector_name d x in
                                          (uu____24293,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24295 =
                                  let uu____24314 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24314, true) in
                                FStar_All.pipe_right uu____24295
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
                              let uu____24353 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24353 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24365::uu____24366 ->
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
                                         let uu____24411 =
                                           let uu____24422 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24422) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24411
                                     | uu____24447 -> tok_typing in
                                   let uu____24456 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24456 with
                                    | (vars',guards',env'',decls_formals,uu____24481)
                                        ->
                                        let uu____24494 =
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
                                        (match uu____24494 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24525 ->
                                                   let uu____24532 =
                                                     let uu____24533 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24533 in
                                                   [uu____24532] in
                                             let encode_elim uu____24543 =
                                               let uu____24544 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24544 with
                                               | (head1,args) ->
                                                   let uu____24587 =
                                                     let uu____24588 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24588.FStar_Syntax_Syntax.n in
                                                   (match uu____24587 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24598;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24599;_},uu____24600)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24606 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24606
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
                                                                 | uu____24649
                                                                    ->
                                                                    let uu____24650
                                                                    =
                                                                    let uu____24651
                                                                    =
                                                                    let uu____24656
                                                                    =
                                                                    let uu____24657
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24657 in
                                                                    (uu____24656,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24651 in
                                                                    FStar_Exn.raise
                                                                    uu____24650 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24673
                                                                    =
                                                                    let uu____24674
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24674 in
                                                                    if
                                                                    uu____24673
                                                                    then
                                                                    let uu____24687
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24687]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24689
                                                               =
                                                               let uu____24702
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24752
                                                                     ->
                                                                    fun
                                                                    uu____24753
                                                                     ->
                                                                    match 
                                                                    (uu____24752,
                                                                    uu____24753)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24848
                                                                    =
                                                                    let uu____24855
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24855 in
                                                                    (match uu____24848
                                                                    with
                                                                    | 
                                                                    (uu____24868,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24876
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24876
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24878
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24878
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
                                                                 uu____24702 in
                                                             (match uu____24689
                                                              with
                                                              | (uu____24893,arg_vars,elim_eqns_or_guards,uu____24896)
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
                                                                    let uu____24926
                                                                    =
                                                                    let uu____24933
                                                                    =
                                                                    let uu____24934
                                                                    =
                                                                    let uu____24945
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24956
                                                                    =
                                                                    let uu____24957
                                                                    =
                                                                    let uu____24962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24962) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24957 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24945,
                                                                    uu____24956) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24934 in
                                                                    (uu____24933,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24926 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24985
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24985,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24987
                                                                    =
                                                                    let uu____24994
                                                                    =
                                                                    let uu____24995
                                                                    =
                                                                    let uu____25006
                                                                    =
                                                                    let uu____25011
                                                                    =
                                                                    let uu____25014
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25014] in
                                                                    [uu____25011] in
                                                                    let uu____25019
                                                                    =
                                                                    let uu____25020
                                                                    =
                                                                    let uu____25025
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25026
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25025,
                                                                    uu____25026) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25020 in
                                                                    (uu____25006,
                                                                    [x],
                                                                    uu____25019) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24995 in
                                                                    let uu____25045
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24994,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25045) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24987
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25052
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
                                                                    (let uu____25080
                                                                    =
                                                                    let uu____25081
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25081
                                                                    dapp1 in
                                                                    [uu____25080]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25052
                                                                    FStar_List.flatten in
                                                                    let uu____25088
                                                                    =
                                                                    let uu____25095
                                                                    =
                                                                    let uu____25096
                                                                    =
                                                                    let uu____25107
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25118
                                                                    =
                                                                    let uu____25119
                                                                    =
                                                                    let uu____25124
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25124) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25119 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25107,
                                                                    uu____25118) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25096 in
                                                                    (uu____25095,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25088) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25145 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25145
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
                                                                 | uu____25188
                                                                    ->
                                                                    let uu____25189
                                                                    =
                                                                    let uu____25190
                                                                    =
                                                                    let uu____25195
                                                                    =
                                                                    let uu____25196
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25196 in
                                                                    (uu____25195,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25190 in
                                                                    FStar_Exn.raise
                                                                    uu____25189 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25212
                                                                    =
                                                                    let uu____25213
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25213 in
                                                                    if
                                                                    uu____25212
                                                                    then
                                                                    let uu____25226
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25226]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25228
                                                               =
                                                               let uu____25241
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25291
                                                                     ->
                                                                    fun
                                                                    uu____25292
                                                                     ->
                                                                    match 
                                                                    (uu____25291,
                                                                    uu____25292)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25387
                                                                    =
                                                                    let uu____25394
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25394 in
                                                                    (match uu____25387
                                                                    with
                                                                    | 
                                                                    (uu____25407,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25415
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25415
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25417
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25417
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
                                                                 uu____25241 in
                                                             (match uu____25228
                                                              with
                                                              | (uu____25432,arg_vars,elim_eqns_or_guards,uu____25435)
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
                                                                    let uu____25465
                                                                    =
                                                                    let uu____25472
                                                                    =
                                                                    let uu____25473
                                                                    =
                                                                    let uu____25484
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25495
                                                                    =
                                                                    let uu____25496
                                                                    =
                                                                    let uu____25501
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25501) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25496 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25484,
                                                                    uu____25495) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25473 in
                                                                    (uu____25472,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25465 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25524
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25524,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25526
                                                                    =
                                                                    let uu____25533
                                                                    =
                                                                    let uu____25534
                                                                    =
                                                                    let uu____25545
                                                                    =
                                                                    let uu____25550
                                                                    =
                                                                    let uu____25553
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25553] in
                                                                    [uu____25550] in
                                                                    let uu____25558
                                                                    =
                                                                    let uu____25559
                                                                    =
                                                                    let uu____25564
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25565
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25564,
                                                                    uu____25565) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25559 in
                                                                    (uu____25545,
                                                                    [x],
                                                                    uu____25558) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25534 in
                                                                    let uu____25584
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25533,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25584) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25526
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25591
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
                                                                    (let uu____25619
                                                                    =
                                                                    let uu____25620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25620
                                                                    dapp1 in
                                                                    [uu____25619]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25591
                                                                    FStar_List.flatten in
                                                                    let uu____25627
                                                                    =
                                                                    let uu____25634
                                                                    =
                                                                    let uu____25635
                                                                    =
                                                                    let uu____25646
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25657
                                                                    =
                                                                    let uu____25658
                                                                    =
                                                                    let uu____25663
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25663) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25658 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25646,
                                                                    uu____25657) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25635 in
                                                                    (uu____25634,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25627) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25682 ->
                                                        ((let uu____25684 =
                                                            let uu____25685 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25686 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25685
                                                              uu____25686 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25684);
                                                         ([], []))) in
                                             let uu____25691 = encode_elim () in
                                             (match uu____25691 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25711 =
                                                      let uu____25714 =
                                                        let uu____25717 =
                                                          let uu____25720 =
                                                            let uu____25723 =
                                                              let uu____25724
                                                                =
                                                                let uu____25735
                                                                  =
                                                                  let uu____25738
                                                                    =
                                                                    let uu____25739
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25739 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25738 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25735) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25724 in
                                                            [uu____25723] in
                                                          let uu____25744 =
                                                            let uu____25747 =
                                                              let uu____25750
                                                                =
                                                                let uu____25753
                                                                  =
                                                                  let uu____25756
                                                                    =
                                                                    let uu____25759
                                                                    =
                                                                    let uu____25762
                                                                    =
                                                                    let uu____25763
                                                                    =
                                                                    let uu____25770
                                                                    =
                                                                    let uu____25771
                                                                    =
                                                                    let uu____25782
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25782) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25771 in
                                                                    (uu____25770,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25763 in
                                                                    let uu____25795
                                                                    =
                                                                    let uu____25798
                                                                    =
                                                                    let uu____25799
                                                                    =
                                                                    let uu____25806
                                                                    =
                                                                    let uu____25807
                                                                    =
                                                                    let uu____25818
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25829
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25818,
                                                                    uu____25829) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25807 in
                                                                    (uu____25806,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25799 in
                                                                    [uu____25798] in
                                                                    uu____25762
                                                                    ::
                                                                    uu____25795 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25759 in
                                                                  FStar_List.append
                                                                    uu____25756
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25753 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25750 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25747 in
                                                          FStar_List.append
                                                            uu____25720
                                                            uu____25744 in
                                                        FStar_List.append
                                                          decls3 uu____25717 in
                                                      FStar_List.append
                                                        decls2 uu____25714 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25711 in
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
           (fun uu____25875  ->
              fun se  ->
                match uu____25875 with
                | (g,env1) ->
                    let uu____25895 = encode_sigelt env1 se in
                    (match uu____25895 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25954 =
        match uu____25954 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25986 ->
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
                 ((let uu____25992 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25992
                   then
                     let uu____25993 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25994 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25995 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25993 uu____25994 uu____25995
                   else ());
                  (let uu____25997 = encode_term t1 env1 in
                   match uu____25997 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26013 =
                         let uu____26020 =
                           let uu____26021 =
                             let uu____26022 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26022
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26021 in
                         new_term_constant_from_string env1 x uu____26020 in
                       (match uu____26013 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26038 = FStar_Options.log_queries () in
                              if uu____26038
                              then
                                let uu____26041 =
                                  let uu____26042 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26043 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26044 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26042 uu____26043 uu____26044 in
                                FStar_Pervasives_Native.Some uu____26041
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26060,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26074 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26074 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26097,se,uu____26099) ->
                 let uu____26104 = encode_sigelt env1 se in
                 (match uu____26104 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26121,se) ->
                 let uu____26127 = encode_sigelt env1 se in
                 (match uu____26127 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26144 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26144 with | (uu____26167,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26182 'Auu____26183 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26183,'Auu____26182)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26251  ->
              match uu____26251 with
              | (l,uu____26263,uu____26264) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26310  ->
              match uu____26310 with
              | (l,uu____26324,uu____26325) ->
                  let uu____26334 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26335 =
                    let uu____26338 =
                      let uu____26339 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26339 in
                    [uu____26338] in
                  uu____26334 :: uu____26335)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26361 =
      let uu____26364 =
        let uu____26365 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26368 =
          let uu____26369 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26369 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26365;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26368
        } in
      [uu____26364] in
    FStar_ST.op_Colon_Equals last_env uu____26361
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26428 = FStar_ST.op_Bang last_env in
      match uu____26428 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26482 ->
          let uu___176_26485 = e in
          let uu____26486 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___176_26485.bindings);
            depth = (uu___176_26485.depth);
            tcenv;
            warn = (uu___176_26485.warn);
            cache = (uu___176_26485.cache);
            nolabels = (uu___176_26485.nolabels);
            use_zfuel_name = (uu___176_26485.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___176_26485.encode_non_total_function_typ);
            current_module_name = uu____26486
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26491 = FStar_ST.op_Bang last_env in
    match uu____26491 with
    | [] -> failwith "Empty env stack"
    | uu____26544::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26601  ->
    let uu____26602 = FStar_ST.op_Bang last_env in
    match uu____26602 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___177_26663 = hd1 in
          {
            bindings = (uu___177_26663.bindings);
            depth = (uu___177_26663.depth);
            tcenv = (uu___177_26663.tcenv);
            warn = (uu___177_26663.warn);
            cache = refs;
            nolabels = (uu___177_26663.nolabels);
            use_zfuel_name = (uu___177_26663.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26663.encode_non_total_function_typ);
            current_module_name = (uu___177_26663.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26717  ->
    let uu____26718 = FStar_ST.op_Bang last_env in
    match uu____26718 with
    | [] -> failwith "Popping an empty stack"
    | uu____26771::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26869::uu____26870,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___178_26878 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___178_26878.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___178_26878.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___178_26878.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26879 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26896 =
        let uu____26899 =
          let uu____26900 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26900 in
        let uu____26901 = open_fact_db_tags env in uu____26899 :: uu____26901 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26896
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
      let uu____26925 = encode_sigelt env se in
      match uu____26925 with
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
        let uu____26963 = FStar_Options.log_queries () in
        if uu____26963
        then
          let uu____26966 =
            let uu____26967 =
              let uu____26968 =
                let uu____26969 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26969 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26968 in
            FStar_SMTEncoding_Term.Caption uu____26967 in
          uu____26966 :: decls
        else decls in
      (let uu____26980 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26980
       then
         let uu____26981 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26981
       else ());
      (let env =
         let uu____26984 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26984 tcenv in
       let uu____26985 = encode_top_level_facts env se in
       match uu____26985 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26999 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26999)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27013 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27013
       then
         let uu____27014 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27014
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27049  ->
                 fun se  ->
                   match uu____27049 with
                   | (g,env2) ->
                       let uu____27069 = encode_top_level_facts env2 se in
                       (match uu____27069 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27092 =
         encode_signature
           (let uu___179_27101 = env in
            {
              bindings = (uu___179_27101.bindings);
              depth = (uu___179_27101.depth);
              tcenv = (uu___179_27101.tcenv);
              warn = false;
              cache = (uu___179_27101.cache);
              nolabels = (uu___179_27101.nolabels);
              use_zfuel_name = (uu___179_27101.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___179_27101.encode_non_total_function_typ);
              current_module_name = (uu___179_27101.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27092 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27118 = FStar_Options.log_queries () in
             if uu____27118
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___180_27126 = env1 in
               {
                 bindings = (uu___180_27126.bindings);
                 depth = (uu___180_27126.depth);
                 tcenv = (uu___180_27126.tcenv);
                 warn = true;
                 cache = (uu___180_27126.cache);
                 nolabels = (uu___180_27126.nolabels);
                 use_zfuel_name = (uu___180_27126.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___180_27126.encode_non_total_function_typ);
                 current_module_name = (uu___180_27126.current_module_name)
               });
            (let uu____27128 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27128
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
        (let uu____27183 =
           let uu____27184 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27184.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27183);
        (let env =
           let uu____27186 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27186 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27198 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27233 = aux rest in
                 (match uu____27233 with
                  | (out,rest1) ->
                      let t =
                        let uu____27263 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27263 with
                        | FStar_Pervasives_Native.Some uu____27268 ->
                            let uu____27269 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27269
                              x.FStar_Syntax_Syntax.sort
                        | uu____27270 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27274 =
                        let uu____27277 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___181_27280 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___181_27280.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___181_27280.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27277 :: out in
                      (uu____27274, rest1))
             | uu____27285 -> ([], bindings1) in
           let uu____27292 = aux bindings in
           match uu____27292 with
           | (closing,bindings1) ->
               let uu____27317 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27317, bindings1) in
         match uu____27198 with
         | (q1,bindings1) ->
             let uu____27340 =
               let uu____27345 =
                 FStar_List.filter
                   (fun uu___146_27350  ->
                      match uu___146_27350 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27351 ->
                          false
                      | uu____27358 -> true) bindings1 in
               encode_env_bindings env uu____27345 in
             (match uu____27340 with
              | (env_decls,env1) ->
                  ((let uu____27376 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27376
                    then
                      let uu____27377 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27377
                    else ());
                   (let uu____27379 = encode_formula q1 env1 in
                    match uu____27379 with
                    | (phi,qdecls) ->
                        let uu____27400 =
                          let uu____27405 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27405 phi in
                        (match uu____27400 with
                         | (labels,phi1) ->
                             let uu____27422 = encode_labels labels in
                             (match uu____27422 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27459 =
                                      let uu____27466 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27467 =
                                        varops.mk_unique "@query" in
                                      (uu____27466,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27467) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27459 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))