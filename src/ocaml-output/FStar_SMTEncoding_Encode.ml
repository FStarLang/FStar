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
      (fun uu___125_119  ->
         match uu___125_119 with
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
        let uu___148_221 = a in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___148_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___148_221.FStar_Syntax_Syntax.sort)
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
    let uu___149_1896 = x in
    let uu____1897 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1897;
      FStar_Syntax_Syntax.index = (uu___149_1896.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___149_1896.FStar_Syntax_Syntax.sort)
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
                 (fun uu___126_2369  ->
                    match uu___126_2369 with
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
           (fun uu___127_2394  ->
              match uu___127_2394 with
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
        (let uu___150_2483 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___150_2483.tcenv);
           warn = (uu___150_2483.warn);
           cache = (uu___150_2483.cache);
           nolabels = (uu___150_2483.nolabels);
           use_zfuel_name = (uu___150_2483.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___150_2483.encode_non_total_function_typ);
           current_module_name = (uu___150_2483.current_module_name)
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
        (let uu___151_2503 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___151_2503.depth);
           tcenv = (uu___151_2503.tcenv);
           warn = (uu___151_2503.warn);
           cache = (uu___151_2503.cache);
           nolabels = (uu___151_2503.nolabels);
           use_zfuel_name = (uu___151_2503.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___151_2503.encode_non_total_function_typ);
           current_module_name = (uu___151_2503.current_module_name)
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
          (let uu___152_2527 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___152_2527.depth);
             tcenv = (uu___152_2527.tcenv);
             warn = (uu___152_2527.warn);
             cache = (uu___152_2527.cache);
             nolabels = (uu___152_2527.nolabels);
             use_zfuel_name = (uu___152_2527.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___152_2527.encode_non_total_function_typ);
             current_module_name = (uu___152_2527.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___153_2540 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___153_2540.depth);
          tcenv = (uu___153_2540.tcenv);
          warn = (uu___153_2540.warn);
          cache = (uu___153_2540.cache);
          nolabels = (uu___153_2540.nolabels);
          use_zfuel_name = (uu___153_2540.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___153_2540.encode_non_total_function_typ);
          current_module_name = (uu___153_2540.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___128_2566  ->
             match uu___128_2566 with
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
        let uu___154_2639 = env in
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
          depth = (uu___154_2639.depth);
          tcenv = (uu___154_2639.tcenv);
          warn = (uu___154_2639.warn);
          cache = (uu___154_2639.cache);
          nolabels = (uu___154_2639.nolabels);
          use_zfuel_name = (uu___154_2639.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___154_2639.encode_non_total_function_typ);
          current_module_name = (uu___154_2639.current_module_name)
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
        (fun uu___129_2704  ->
           match uu___129_2704 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2743 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2762 =
        lookup_binding env
          (fun uu___130_2770  ->
             match uu___130_2770 with
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
          let uu___155_2892 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___155_2892.depth);
            tcenv = (uu___155_2892.tcenv);
            warn = (uu___155_2892.warn);
            cache = (uu___155_2892.cache);
            nolabels = (uu___155_2892.nolabels);
            use_zfuel_name = (uu___155_2892.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_2892.encode_non_total_function_typ);
            current_module_name = (uu___155_2892.current_module_name)
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
            let uu___156_2947 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___156_2947.depth);
              tcenv = (uu___156_2947.tcenv);
              warn = (uu___156_2947.warn);
              cache = (uu___156_2947.cache);
              nolabels = (uu___156_2947.nolabels);
              use_zfuel_name = (uu___156_2947.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_2947.encode_non_total_function_typ);
              current_module_name = (uu___156_2947.current_module_name)
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
        (fun uu___131_3201  ->
           match uu___131_3201 with
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
               (fun uu___132_3528  ->
                  match uu___132_3528 with
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
  fun uu___133_3636  ->
    match uu___133_3636 with
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
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6219 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6219 with
            | (binders1,res) ->
                let uu____6230 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6230
                then
                  let uu____6235 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6235 with
                   | (vars,guards,env',decls,uu____6260) ->
                       let fsym =
                         let uu____6278 = varops.fresh "f" in
                         (uu____6278, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6281 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___157_6290 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___157_6290.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___157_6290.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___157_6290.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___157_6290.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___157_6290.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___157_6290.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___157_6290.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___157_6290.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___157_6290.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___157_6290.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___157_6290.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___157_6290.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___157_6290.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___157_6290.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___157_6290.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___157_6290.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___157_6290.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___157_6290.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___157_6290.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___157_6290.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___157_6290.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___157_6290.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___157_6290.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___157_6290.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___157_6290.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___157_6290.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___157_6290.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___157_6290.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___157_6290.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___157_6290.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___157_6290.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___157_6290.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6281 with
                        | (pre_opt,res_t) ->
                            let uu____6301 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6301 with
                             | (res_pred,decls') ->
                                 let uu____6312 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6325 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6325, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6329 =
                                         encode_formula pre env' in
                                       (match uu____6329 with
                                        | (guard,decls0) ->
                                            let uu____6342 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6342, decls0)) in
                                 (match uu____6312 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6354 =
                                          let uu____6365 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6365) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6354 in
                                      let cvars =
                                        let uu____6383 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6383
                                          (FStar_List.filter
                                             (fun uu____6397  ->
                                                match uu____6397 with
                                                | (x,uu____6403) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6422 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6422 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6430 =
                                             let uu____6431 =
                                               let uu____6438 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6438) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6431 in
                                           (uu____6430,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6458 =
                                               let uu____6459 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6459 in
                                             varops.mk_unique uu____6458 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6470 =
                                               FStar_Options.log_queries () in
                                             if uu____6470
                                             then
                                               let uu____6473 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6473
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6481 =
                                               let uu____6488 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6488) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6481 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6500 =
                                               let uu____6507 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6507,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6500 in
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
                                             let uu____6528 =
                                               let uu____6535 =
                                                 let uu____6536 =
                                                   let uu____6547 =
                                                     let uu____6548 =
                                                       let uu____6553 =
                                                         let uu____6554 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6554 in
                                                       (f_has_t, uu____6553) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6548 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6547) in
                                                 mkForall_fuel uu____6536 in
                                               (uu____6535,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6528 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6577 =
                                               let uu____6584 =
                                                 let uu____6585 =
                                                   let uu____6596 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6596) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6585 in
                                               (uu____6584,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6577 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6621 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6621);
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
                     let uu____6636 =
                       let uu____6643 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6643,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6636 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6655 =
                       let uu____6662 =
                         let uu____6663 =
                           let uu____6674 =
                             let uu____6675 =
                               let uu____6680 =
                                 let uu____6681 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6681 in
                               (f_has_t, uu____6680) in
                             FStar_SMTEncoding_Util.mkImp uu____6675 in
                           ([[f_has_t]], [fsym], uu____6674) in
                         mkForall_fuel uu____6663 in
                       (uu____6662, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6655 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6708 ->
           let uu____6715 =
             let uu____6720 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6720 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6727;
                 FStar_Syntax_Syntax.vars = uu____6728;_} ->
                 let uu____6735 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6735 with
                  | (b,f1) ->
                      let uu____6760 =
                        let uu____6761 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6761 in
                      (uu____6760, f1))
             | uu____6770 -> failwith "impossible" in
           (match uu____6715 with
            | (x,f) ->
                let uu____6781 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6781 with
                 | (base_t,decls) ->
                     let uu____6792 = gen_term_var env x in
                     (match uu____6792 with
                      | (x1,xtm,env') ->
                          let uu____6806 = encode_formula f env' in
                          (match uu____6806 with
                           | (refinement,decls') ->
                               let uu____6817 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6817 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6833 =
                                        let uu____6836 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6843 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6836
                                          uu____6843 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6833 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6876  ->
                                              match uu____6876 with
                                              | (y,uu____6882) ->
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
                                    let uu____6915 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6915 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6923 =
                                           let uu____6924 =
                                             let uu____6931 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6931) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6924 in
                                         (uu____6923,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6952 =
                                             let uu____6953 =
                                               let uu____6954 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6954 in
                                             Prims.strcat module_name
                                               uu____6953 in
                                           varops.mk_unique uu____6952 in
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
                                           let uu____6968 =
                                             let uu____6975 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6975) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6968 in
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
                                           let uu____6990 =
                                             let uu____6997 =
                                               let uu____6998 =
                                                 let uu____7009 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7009) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6998 in
                                             (uu____6997,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6990 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7035 =
                                             let uu____7042 =
                                               let uu____7043 =
                                                 let uu____7054 =
                                                   let uu____7055 =
                                                     let uu____7060 =
                                                       let uu____7061 =
                                                         let uu____7072 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7072) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7061 in
                                                     (uu____7060, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7055 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7054) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7043 in
                                             (uu____7042,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7035 in
                                         let t_kinding =
                                           let uu____7110 =
                                             let uu____7117 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7117,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7110 in
                                         let t_interp =
                                           let uu____7135 =
                                             let uu____7142 =
                                               let uu____7143 =
                                                 let uu____7154 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7154) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7143 in
                                             let uu____7177 =
                                               let uu____7180 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7180 in
                                             (uu____7142, uu____7177,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7135 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7187 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7187);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7217 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7217 in
           let uu____7218 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7218 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7230 =
                    let uu____7237 =
                      let uu____7238 =
                        let uu____7239 =
                          let uu____7240 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7240 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7239 in
                      varops.mk_unique uu____7238 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7237) in
                  FStar_SMTEncoding_Util.mkAssume uu____7230 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7245 ->
           let uu____7260 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7260 with
            | (head1,args_e) ->
                let uu____7301 =
                  let uu____7314 =
                    let uu____7315 = FStar_Syntax_Subst.compress head1 in
                    uu____7315.FStar_Syntax_Syntax.n in
                  (uu____7314, args_e) in
                (match uu____7301 with
                 | uu____7330 when head_redex env head1 ->
                     let uu____7343 = whnf env t in
                     encode_term uu____7343 env
                 | uu____7344 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7363 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7377;
                       FStar_Syntax_Syntax.vars = uu____7378;_},uu____7379),uu____7380::
                    (v1,uu____7382)::(v2,uu____7384)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7435 = encode_term v1 env in
                     (match uu____7435 with
                      | (v11,decls1) ->
                          let uu____7446 = encode_term v2 env in
                          (match uu____7446 with
                           | (v21,decls2) ->
                               let uu____7457 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7457,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7461::(v1,uu____7463)::(v2,uu____7465)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7512 = encode_term v1 env in
                     (match uu____7512 with
                      | (v11,decls1) ->
                          let uu____7523 = encode_term v2 env in
                          (match uu____7523 with
                           | (v21,decls2) ->
                               let uu____7534 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7534,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7537) ->
                     let e0 =
                       let uu____7555 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7555 in
                     ((let uu____7563 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7563
                       then
                         let uu____7564 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7564
                       else ());
                      (let e =
                         let uu____7569 =
                           let uu____7570 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7571 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7570
                             uu____7571 in
                         uu____7569 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7580),(arg,uu____7582)::[]) -> encode_term arg env
                 | uu____7607 ->
                     let uu____7620 = encode_args args_e env in
                     (match uu____7620 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7675 = encode_term head1 env in
                            match uu____7675 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7739 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7739 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7817  ->
                                                 fun uu____7818  ->
                                                   match (uu____7817,
                                                           uu____7818)
                                                   with
                                                   | ((bv,uu____7840),
                                                      (a,uu____7842)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7860 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7860
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7865 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7865 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7880 =
                                                   let uu____7887 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7896 =
                                                     let uu____7897 =
                                                       let uu____7898 =
                                                         let uu____7899 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7899 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7898 in
                                                     varops.mk_unique
                                                       uu____7897 in
                                                   (uu____7887,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7896) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7880 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7916 = lookup_free_var_sym env fv in
                            match uu____7916 with
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
                                   FStar_Syntax_Syntax.pos = uu____7947;
                                   FStar_Syntax_Syntax.vars = uu____7948;_},uu____7949)
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
                                   FStar_Syntax_Syntax.pos = uu____7960;
                                   FStar_Syntax_Syntax.vars = uu____7961;_},uu____7962)
                                ->
                                let uu____7967 =
                                  let uu____7968 =
                                    let uu____7973 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7973
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7968
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7967
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8003 =
                                  let uu____8004 =
                                    let uu____8009 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8009
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8004
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8003
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8038,(FStar_Util.Inl t1,uu____8040),uu____8041)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8090,(FStar_Util.Inr c,uu____8092),uu____8093)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8142 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8169 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8169 in
                               let uu____8170 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8170 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8186;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8187;_},uu____8188)
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
                                     | uu____8202 ->
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
           let uu____8251 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8251 with
            | (bs1,body1,opening) ->
                let fallback uu____8274 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8281 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8281, [decl]) in
                let is_impure rc =
                  let uu____8288 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8288 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8298 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8298
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8318 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8318
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8322 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8322)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8329 =
                         let uu____8330 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8330 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8329);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8332 =
                       (is_impure rc) &&
                         (let uu____8334 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8334) in
                     if uu____8332
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8341 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8341 with
                        | (vars,guards,envbody,decls,uu____8366) ->
                            let body2 =
                              let uu____8380 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8380
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8382 = encode_term body2 envbody in
                            (match uu____8382 with
                             | (body3,decls') ->
                                 let uu____8393 =
                                   let uu____8402 = codomain_eff rc in
                                   match uu____8402 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8421 = encode_term tfun env in
                                       (match uu____8421 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8393 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8453 =
                                          let uu____8464 =
                                            let uu____8465 =
                                              let uu____8470 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8470, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8465 in
                                          ([], vars, uu____8464) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8453 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8482 =
                                              let uu____8485 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8485
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8482 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8504 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8504 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8512 =
                                             let uu____8513 =
                                               let uu____8520 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8520) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8513 in
                                           (uu____8512,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8531 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8531 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8542 =
                                                    let uu____8543 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8543 = cache_size in
                                                  if uu____8542
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
                                                    let uu____8559 =
                                                      let uu____8560 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8560 in
                                                    varops.mk_unique
                                                      uu____8559 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8567 =
                                                    let uu____8574 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8574) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8567 in
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
                                                      let uu____8592 =
                                                        let uu____8593 =
                                                          let uu____8600 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8600,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8593 in
                                                      [uu____8592] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8613 =
                                                    let uu____8620 =
                                                      let uu____8621 =
                                                        let uu____8632 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8632) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8621 in
                                                    (uu____8620,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8613 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8649 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8649);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8652,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8653;
                          FStar_Syntax_Syntax.lbunivs = uu____8654;
                          FStar_Syntax_Syntax.lbtyp = uu____8655;
                          FStar_Syntax_Syntax.lbeff = uu____8656;
                          FStar_Syntax_Syntax.lbdef = uu____8657;_}::uu____8658),uu____8659)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8685;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8687;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8708 ->
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
              let uu____8778 = encode_term e1 env in
              match uu____8778 with
              | (ee1,decls1) ->
                  let uu____8789 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8789 with
                   | (xs,e21) ->
                       let uu____8814 = FStar_List.hd xs in
                       (match uu____8814 with
                        | (x1,uu____8828) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8830 = encode_body e21 env' in
                            (match uu____8830 with
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
            let uu____8862 =
              let uu____8869 =
                let uu____8870 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8870 in
              gen_term_var env uu____8869 in
            match uu____8862 with
            | (scrsym,scr',env1) ->
                let uu____8878 = encode_term e env1 in
                (match uu____8878 with
                 | (scr,decls) ->
                     let uu____8889 =
                       let encode_branch b uu____8914 =
                         match uu____8914 with
                         | (else_case,decls1) ->
                             let uu____8933 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8933 with
                              | (p,w,br) ->
                                  let uu____8959 = encode_pat env1 p in
                                  (match uu____8959 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8996  ->
                                                   match uu____8996 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9003 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9025 =
                                               encode_term w1 env2 in
                                             (match uu____9025 with
                                              | (w2,decls2) ->
                                                  let uu____9038 =
                                                    let uu____9039 =
                                                      let uu____9044 =
                                                        let uu____9045 =
                                                          let uu____9050 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9050) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9045 in
                                                      (guard, uu____9044) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9039 in
                                                  (uu____9038, decls2)) in
                                       (match uu____9003 with
                                        | (guard1,decls2) ->
                                            let uu____9063 =
                                              encode_br br env2 in
                                            (match uu____9063 with
                                             | (br1,decls3) ->
                                                 let uu____9076 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9076,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8889 with
                      | (match_tm,decls1) ->
                          let uu____9095 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9095, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9135 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9135
       then
         let uu____9136 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9136
       else ());
      (let uu____9138 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9138 with
       | (vars,pat_term) ->
           let uu____9155 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9208  ->
                     fun v1  ->
                       match uu____9208 with
                       | (env1,vars1) ->
                           let uu____9260 = gen_term_var env1 v1 in
                           (match uu____9260 with
                            | (xx,uu____9282,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9155 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9361 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9362 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9363 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9371 = encode_const c env1 in
                      (match uu____9371 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9385::uu____9386 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9389 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9412 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9412 with
                        | (uu____9419,uu____9420::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9423 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9456  ->
                                  match uu____9456 with
                                  | (arg,uu____9464) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9470 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9470)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9497) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9528 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9551 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9595  ->
                                  match uu____9595 with
                                  | (arg,uu____9609) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9615 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9615)) in
                      FStar_All.pipe_right uu____9551 FStar_List.flatten in
                let pat_term1 uu____9643 = encode_term pat_term env1 in
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
      let uu____9653 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9691  ->
                fun uu____9692  ->
                  match (uu____9691, uu____9692) with
                  | ((tms,decls),(t,uu____9728)) ->
                      let uu____9749 = encode_term t env in
                      (match uu____9749 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9653 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9806 = FStar_Syntax_Util.list_elements e in
        match uu____9806 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9827 =
          let uu____9842 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9842 FStar_Syntax_Util.head_and_args in
        match uu____9827 with
        | (head1,args) ->
            let uu____9881 =
              let uu____9894 =
                let uu____9895 = FStar_Syntax_Util.un_uinst head1 in
                uu____9895.FStar_Syntax_Syntax.n in
              (uu____9894, args) in
            (match uu____9881 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9909,uu____9910)::(e,uu____9912)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9947 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9983 =
            let uu____9998 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9998 FStar_Syntax_Util.head_and_args in
          match uu____9983 with
          | (head1,args) ->
              let uu____10039 =
                let uu____10052 =
                  let uu____10053 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10053.FStar_Syntax_Syntax.n in
                (uu____10052, args) in
              (match uu____10039 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10070)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10097 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10119 = smt_pat_or1 t1 in
            (match uu____10119 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10135 = list_elements1 e in
                 FStar_All.pipe_right uu____10135
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10153 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10153
                           (FStar_List.map one_pat)))
             | uu____10164 ->
                 let uu____10169 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10169])
        | uu____10190 ->
            let uu____10193 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10193] in
      let uu____10214 =
        let uu____10233 =
          let uu____10234 = FStar_Syntax_Subst.compress t in
          uu____10234.FStar_Syntax_Syntax.n in
        match uu____10233 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10273 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10273 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10316;
                        FStar_Syntax_Syntax.effect_name = uu____10317;
                        FStar_Syntax_Syntax.result_typ = uu____10318;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10320)::(post,uu____10322)::(pats,uu____10324)::[];
                        FStar_Syntax_Syntax.flags = uu____10325;_}
                      ->
                      let uu____10366 = lemma_pats pats in
                      (binders1, pre, post, uu____10366)
                  | uu____10383 -> failwith "impos"))
        | uu____10402 -> failwith "Impos" in
      match uu____10214 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___158_10450 = env in
            {
              bindings = (uu___158_10450.bindings);
              depth = (uu___158_10450.depth);
              tcenv = (uu___158_10450.tcenv);
              warn = (uu___158_10450.warn);
              cache = (uu___158_10450.cache);
              nolabels = (uu___158_10450.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___158_10450.encode_non_total_function_typ);
              current_module_name = (uu___158_10450.current_module_name)
            } in
          let uu____10451 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10451 with
           | (vars,guards,env2,decls,uu____10476) ->
               let uu____10489 =
                 let uu____10502 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10546 =
                             let uu____10555 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10555
                               FStar_List.unzip in
                           match uu____10546 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10502 FStar_List.unzip in
               (match uu____10489 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___159_10664 = env2 in
                      {
                        bindings = (uu___159_10664.bindings);
                        depth = (uu___159_10664.depth);
                        tcenv = (uu___159_10664.tcenv);
                        warn = (uu___159_10664.warn);
                        cache = (uu___159_10664.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___159_10664.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___159_10664.encode_non_total_function_typ);
                        current_module_name =
                          (uu___159_10664.current_module_name)
                      } in
                    let uu____10665 =
                      let uu____10670 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10670 env3 in
                    (match uu____10665 with
                     | (pre1,decls'') ->
                         let uu____10677 =
                           let uu____10682 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10682 env3 in
                         (match uu____10677 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10692 =
                                let uu____10693 =
                                  let uu____10704 =
                                    let uu____10705 =
                                      let uu____10710 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10710, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10705 in
                                  (pats, vars, uu____10704) in
                                FStar_SMTEncoding_Util.mkForall uu____10693 in
                              (uu____10692, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10729 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10729
        then
          let uu____10730 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10731 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10730 uu____10731
        else () in
      let enc f r l =
        let uu____10764 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10792 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10792 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10764 with
        | (decls,args) ->
            let uu____10821 =
              let uu___160_10822 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_10822.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_10822.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10821, decls) in
      let const_op f r uu____10853 =
        let uu____10866 = f r in (uu____10866, []) in
      let un_op f l =
        let uu____10885 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10885 in
      let bin_op f uu___134_10901 =
        match uu___134_10901 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10912 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10946 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10969  ->
                 match uu____10969 with
                 | (t,uu____10983) ->
                     let uu____10984 = encode_formula t env in
                     (match uu____10984 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10946 with
        | (decls,phis) ->
            let uu____11013 =
              let uu___161_11014 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___161_11014.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___161_11014.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11013, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11075  ->
               match uu____11075 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11094) -> false
                    | uu____11095 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11110 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11110
        else
          (let uu____11124 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11124 r rf) in
      let mk_imp1 r uu___135_11149 =
        match uu___135_11149 with
        | (lhs,uu____11155)::(rhs,uu____11157)::[] ->
            let uu____11184 = encode_formula rhs env in
            (match uu____11184 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11199) ->
                      (l1, decls1)
                  | uu____11204 ->
                      let uu____11205 = encode_formula lhs env in
                      (match uu____11205 with
                       | (l2,decls2) ->
                           let uu____11216 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11216, (FStar_List.append decls1 decls2)))))
        | uu____11219 -> failwith "impossible" in
      let mk_ite r uu___136_11240 =
        match uu___136_11240 with
        | (guard,uu____11246)::(_then,uu____11248)::(_else,uu____11250)::[]
            ->
            let uu____11287 = encode_formula guard env in
            (match uu____11287 with
             | (g,decls1) ->
                 let uu____11298 = encode_formula _then env in
                 (match uu____11298 with
                  | (t,decls2) ->
                      let uu____11309 = encode_formula _else env in
                      (match uu____11309 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11323 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11348 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11348 in
      let connectives =
        let uu____11366 =
          let uu____11379 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11379) in
        let uu____11396 =
          let uu____11411 =
            let uu____11424 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11424) in
          let uu____11441 =
            let uu____11456 =
              let uu____11471 =
                let uu____11484 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11484) in
              let uu____11501 =
                let uu____11516 =
                  let uu____11531 =
                    let uu____11544 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11544) in
                  [uu____11531;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11516 in
              uu____11471 :: uu____11501 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11456 in
          uu____11411 :: uu____11441 in
        uu____11366 :: uu____11396 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11865 = encode_formula phi' env in
            (match uu____11865 with
             | (phi2,decls) ->
                 let uu____11876 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11876, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11877 ->
            let uu____11884 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11884 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11923 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11923 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11935;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11937;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11958 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11958 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12005::(x,uu____12007)::(t,uu____12009)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12056 = encode_term x env in
                 (match uu____12056 with
                  | (x1,decls) ->
                      let uu____12067 = encode_term t env in
                      (match uu____12067 with
                       | (t1,decls') ->
                           let uu____12078 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12078, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12083)::(msg,uu____12085)::(phi2,uu____12087)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12132 =
                   let uu____12137 =
                     let uu____12138 = FStar_Syntax_Subst.compress r in
                     uu____12138.FStar_Syntax_Syntax.n in
                   let uu____12141 =
                     let uu____12142 = FStar_Syntax_Subst.compress msg in
                     uu____12142.FStar_Syntax_Syntax.n in
                   (uu____12137, uu____12141) in
                 (match uu____12132 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12151))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12157 -> fallback phi2)
             | uu____12162 when head_redex env head2 ->
                 let uu____12175 = whnf env phi1 in
                 encode_formula uu____12175 env
             | uu____12176 ->
                 let uu____12189 = encode_term phi1 env in
                 (match uu____12189 with
                  | (tt,decls) ->
                      let uu____12200 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___162_12203 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___162_12203.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___162_12203.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12200, decls)))
        | uu____12204 ->
            let uu____12205 = encode_term phi1 env in
            (match uu____12205 with
             | (tt,decls) ->
                 let uu____12216 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___163_12219 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___163_12219.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___163_12219.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12216, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12255 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12255 with
        | (vars,guards,env2,decls,uu____12294) ->
            let uu____12307 =
              let uu____12320 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12368 =
                          let uu____12377 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12407  ->
                                    match uu____12407 with
                                    | (t,uu____12417) ->
                                        encode_term t
                                          (let uu___164_12419 = env2 in
                                           {
                                             bindings =
                                               (uu___164_12419.bindings);
                                             depth = (uu___164_12419.depth);
                                             tcenv = (uu___164_12419.tcenv);
                                             warn = (uu___164_12419.warn);
                                             cache = (uu___164_12419.cache);
                                             nolabels =
                                               (uu___164_12419.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___164_12419.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___164_12419.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12377 FStar_List.unzip in
                        match uu____12368 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12320 FStar_List.unzip in
            (match uu____12307 with
             | (pats,decls') ->
                 let uu____12518 = encode_formula body env2 in
                 (match uu____12518 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12550;
                             FStar_SMTEncoding_Term.rng = uu____12551;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12566 -> guards in
                      let uu____12571 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12571, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12631  ->
                   match uu____12631 with
                   | (x,uu____12637) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12645 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12657 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12657) uu____12645 tl1 in
             let uu____12660 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12687  ->
                       match uu____12687 with
                       | (b,uu____12693) ->
                           let uu____12694 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12694)) in
             (match uu____12660 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12700) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12714 =
                    let uu____12715 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12715 in
                  FStar_Errors.warn pos uu____12714) in
       let uu____12716 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12716 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12725 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12783  ->
                     match uu____12783 with
                     | (l,uu____12797) -> FStar_Ident.lid_equals op l)) in
           (match uu____12725 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12830,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12870 = encode_q_body env vars pats body in
             match uu____12870 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12915 =
                     let uu____12926 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12926) in
                   FStar_SMTEncoding_Term.mkForall uu____12915
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12945 = encode_q_body env vars pats body in
             match uu____12945 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12989 =
                   let uu____12990 =
                     let uu____13001 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13001) in
                   FStar_SMTEncoding_Term.mkExists uu____12990
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12989, decls))))
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
  let uu____13099 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13099 with
  | (asym,a) ->
      let uu____13106 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13106 with
       | (xsym,x) ->
           let uu____13113 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13113 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13157 =
                      let uu____13168 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13168, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13157 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13194 =
                      let uu____13201 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13201) in
                    FStar_SMTEncoding_Util.mkApp uu____13194 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13214 =
                    let uu____13217 =
                      let uu____13220 =
                        let uu____13223 =
                          let uu____13224 =
                            let uu____13231 =
                              let uu____13232 =
                                let uu____13243 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13243) in
                              FStar_SMTEncoding_Util.mkForall uu____13232 in
                            (uu____13231, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13224 in
                        let uu____13260 =
                          let uu____13263 =
                            let uu____13264 =
                              let uu____13271 =
                                let uu____13272 =
                                  let uu____13283 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13283) in
                                FStar_SMTEncoding_Util.mkForall uu____13272 in
                              (uu____13271,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13264 in
                          [uu____13263] in
                        uu____13223 :: uu____13260 in
                      xtok_decl :: uu____13220 in
                    xname_decl :: uu____13217 in
                  (xtok1, uu____13214) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13374 =
                    let uu____13387 =
                      let uu____13396 =
                        let uu____13397 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13397 in
                      quant axy uu____13396 in
                    (FStar_Parser_Const.op_Eq, uu____13387) in
                  let uu____13406 =
                    let uu____13421 =
                      let uu____13434 =
                        let uu____13443 =
                          let uu____13444 =
                            let uu____13445 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13445 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13444 in
                        quant axy uu____13443 in
                      (FStar_Parser_Const.op_notEq, uu____13434) in
                    let uu____13454 =
                      let uu____13469 =
                        let uu____13482 =
                          let uu____13491 =
                            let uu____13492 =
                              let uu____13493 =
                                let uu____13498 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13499 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13498, uu____13499) in
                              FStar_SMTEncoding_Util.mkLT uu____13493 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13492 in
                          quant xy uu____13491 in
                        (FStar_Parser_Const.op_LT, uu____13482) in
                      let uu____13508 =
                        let uu____13523 =
                          let uu____13536 =
                            let uu____13545 =
                              let uu____13546 =
                                let uu____13547 =
                                  let uu____13552 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13553 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13552, uu____13553) in
                                FStar_SMTEncoding_Util.mkLTE uu____13547 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13546 in
                            quant xy uu____13545 in
                          (FStar_Parser_Const.op_LTE, uu____13536) in
                        let uu____13562 =
                          let uu____13577 =
                            let uu____13590 =
                              let uu____13599 =
                                let uu____13600 =
                                  let uu____13601 =
                                    let uu____13606 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13607 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13606, uu____13607) in
                                  FStar_SMTEncoding_Util.mkGT uu____13601 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13600 in
                              quant xy uu____13599 in
                            (FStar_Parser_Const.op_GT, uu____13590) in
                          let uu____13616 =
                            let uu____13631 =
                              let uu____13644 =
                                let uu____13653 =
                                  let uu____13654 =
                                    let uu____13655 =
                                      let uu____13660 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13661 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13660, uu____13661) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13655 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13654 in
                                quant xy uu____13653 in
                              (FStar_Parser_Const.op_GTE, uu____13644) in
                            let uu____13670 =
                              let uu____13685 =
                                let uu____13698 =
                                  let uu____13707 =
                                    let uu____13708 =
                                      let uu____13709 =
                                        let uu____13714 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13715 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13714, uu____13715) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13709 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13708 in
                                  quant xy uu____13707 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13698) in
                              let uu____13724 =
                                let uu____13739 =
                                  let uu____13752 =
                                    let uu____13761 =
                                      let uu____13762 =
                                        let uu____13763 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13763 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13762 in
                                    quant qx uu____13761 in
                                  (FStar_Parser_Const.op_Minus, uu____13752) in
                                let uu____13772 =
                                  let uu____13787 =
                                    let uu____13800 =
                                      let uu____13809 =
                                        let uu____13810 =
                                          let uu____13811 =
                                            let uu____13816 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13817 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13816, uu____13817) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13811 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13810 in
                                      quant xy uu____13809 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13800) in
                                  let uu____13826 =
                                    let uu____13841 =
                                      let uu____13854 =
                                        let uu____13863 =
                                          let uu____13864 =
                                            let uu____13865 =
                                              let uu____13870 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13871 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13870, uu____13871) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13865 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13864 in
                                        quant xy uu____13863 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13854) in
                                    let uu____13880 =
                                      let uu____13895 =
                                        let uu____13908 =
                                          let uu____13917 =
                                            let uu____13918 =
                                              let uu____13919 =
                                                let uu____13924 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13925 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13924, uu____13925) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13919 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13918 in
                                          quant xy uu____13917 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13908) in
                                      let uu____13934 =
                                        let uu____13949 =
                                          let uu____13962 =
                                            let uu____13971 =
                                              let uu____13972 =
                                                let uu____13973 =
                                                  let uu____13978 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13979 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13978, uu____13979) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13973 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13972 in
                                            quant xy uu____13971 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13962) in
                                        let uu____13988 =
                                          let uu____14003 =
                                            let uu____14016 =
                                              let uu____14025 =
                                                let uu____14026 =
                                                  let uu____14027 =
                                                    let uu____14032 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14033 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14032,
                                                      uu____14033) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14027 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14026 in
                                              quant xy uu____14025 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14016) in
                                          let uu____14042 =
                                            let uu____14057 =
                                              let uu____14070 =
                                                let uu____14079 =
                                                  let uu____14080 =
                                                    let uu____14081 =
                                                      let uu____14086 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14087 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14086,
                                                        uu____14087) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14081 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14080 in
                                                quant xy uu____14079 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14070) in
                                            let uu____14096 =
                                              let uu____14111 =
                                                let uu____14124 =
                                                  let uu____14133 =
                                                    let uu____14134 =
                                                      let uu____14135 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14135 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14134 in
                                                  quant qx uu____14133 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14124) in
                                              [uu____14111] in
                                            uu____14057 :: uu____14096 in
                                          uu____14003 :: uu____14042 in
                                        uu____13949 :: uu____13988 in
                                      uu____13895 :: uu____13934 in
                                    uu____13841 :: uu____13880 in
                                  uu____13787 :: uu____13826 in
                                uu____13739 :: uu____13772 in
                              uu____13685 :: uu____13724 in
                            uu____13631 :: uu____13670 in
                          uu____13577 :: uu____13616 in
                        uu____13523 :: uu____13562 in
                      uu____13469 :: uu____13508 in
                    uu____13421 :: uu____13454 in
                  uu____13374 :: uu____13406 in
                let mk1 l v1 =
                  let uu____14349 =
                    let uu____14358 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14416  ->
                              match uu____14416 with
                              | (l',uu____14430) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14358
                      (FStar_Option.map
                         (fun uu____14490  ->
                            match uu____14490 with | (uu____14509,b) -> b v1)) in
                  FStar_All.pipe_right uu____14349 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14580  ->
                          match uu____14580 with
                          | (l',uu____14594) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14635 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14635 with
        | (xxsym,xx) ->
            let uu____14642 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14642 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14652 =
                   let uu____14659 =
                     let uu____14660 =
                       let uu____14671 =
                         let uu____14672 =
                           let uu____14677 =
                             let uu____14678 =
                               let uu____14683 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14683) in
                             FStar_SMTEncoding_Util.mkEq uu____14678 in
                           (xx_has_type, uu____14677) in
                         FStar_SMTEncoding_Util.mkImp uu____14672 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14671) in
                     FStar_SMTEncoding_Util.mkForall uu____14660 in
                   let uu____14708 =
                     let uu____14709 =
                       let uu____14710 =
                         let uu____14711 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14711 in
                       Prims.strcat module_name uu____14710 in
                     varops.mk_unique uu____14709 in
                   (uu____14659, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14708) in
                 FStar_SMTEncoding_Util.mkAssume uu____14652)
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
    let uu____14751 =
      let uu____14752 =
        let uu____14759 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14759, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14752 in
    let uu____14762 =
      let uu____14765 =
        let uu____14766 =
          let uu____14773 =
            let uu____14774 =
              let uu____14785 =
                let uu____14786 =
                  let uu____14791 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14791) in
                FStar_SMTEncoding_Util.mkImp uu____14786 in
              ([[typing_pred]], [xx], uu____14785) in
            mkForall_fuel uu____14774 in
          (uu____14773, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14766 in
      [uu____14765] in
    uu____14751 :: uu____14762 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14833 =
      let uu____14834 =
        let uu____14841 =
          let uu____14842 =
            let uu____14853 =
              let uu____14858 =
                let uu____14861 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14861] in
              [uu____14858] in
            let uu____14866 =
              let uu____14867 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14867 tt in
            (uu____14853, [bb], uu____14866) in
          FStar_SMTEncoding_Util.mkForall uu____14842 in
        (uu____14841, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14834 in
    let uu____14888 =
      let uu____14891 =
        let uu____14892 =
          let uu____14899 =
            let uu____14900 =
              let uu____14911 =
                let uu____14912 =
                  let uu____14917 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14917) in
                FStar_SMTEncoding_Util.mkImp uu____14912 in
              ([[typing_pred]], [xx], uu____14911) in
            mkForall_fuel uu____14900 in
          (uu____14899, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14892 in
      [uu____14891] in
    uu____14833 :: uu____14888 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14967 =
        let uu____14968 =
          let uu____14975 =
            let uu____14978 =
              let uu____14981 =
                let uu____14984 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14985 =
                  let uu____14988 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14988] in
                uu____14984 :: uu____14985 in
              tt :: uu____14981 in
            tt :: uu____14978 in
          ("Prims.Precedes", uu____14975) in
        FStar_SMTEncoding_Util.mkApp uu____14968 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14967 in
    let precedes_y_x =
      let uu____14992 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14992 in
    let uu____14995 =
      let uu____14996 =
        let uu____15003 =
          let uu____15004 =
            let uu____15015 =
              let uu____15020 =
                let uu____15023 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15023] in
              [uu____15020] in
            let uu____15028 =
              let uu____15029 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15029 tt in
            (uu____15015, [bb], uu____15028) in
          FStar_SMTEncoding_Util.mkForall uu____15004 in
        (uu____15003, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14996 in
    let uu____15050 =
      let uu____15053 =
        let uu____15054 =
          let uu____15061 =
            let uu____15062 =
              let uu____15073 =
                let uu____15074 =
                  let uu____15079 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15079) in
                FStar_SMTEncoding_Util.mkImp uu____15074 in
              ([[typing_pred]], [xx], uu____15073) in
            mkForall_fuel uu____15062 in
          (uu____15061, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15054 in
      let uu____15104 =
        let uu____15107 =
          let uu____15108 =
            let uu____15115 =
              let uu____15116 =
                let uu____15127 =
                  let uu____15128 =
                    let uu____15133 =
                      let uu____15134 =
                        let uu____15137 =
                          let uu____15140 =
                            let uu____15143 =
                              let uu____15144 =
                                let uu____15149 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15150 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15149, uu____15150) in
                              FStar_SMTEncoding_Util.mkGT uu____15144 in
                            let uu____15151 =
                              let uu____15154 =
                                let uu____15155 =
                                  let uu____15160 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15161 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15160, uu____15161) in
                                FStar_SMTEncoding_Util.mkGTE uu____15155 in
                              let uu____15162 =
                                let uu____15165 =
                                  let uu____15166 =
                                    let uu____15171 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15172 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15171, uu____15172) in
                                  FStar_SMTEncoding_Util.mkLT uu____15166 in
                                [uu____15165] in
                              uu____15154 :: uu____15162 in
                            uu____15143 :: uu____15151 in
                          typing_pred_y :: uu____15140 in
                        typing_pred :: uu____15137 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15134 in
                    (uu____15133, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15128 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15127) in
              mkForall_fuel uu____15116 in
            (uu____15115,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15108 in
        [uu____15107] in
      uu____15053 :: uu____15104 in
    uu____14995 :: uu____15050 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15218 =
      let uu____15219 =
        let uu____15226 =
          let uu____15227 =
            let uu____15238 =
              let uu____15243 =
                let uu____15246 = FStar_SMTEncoding_Term.boxString b in
                [uu____15246] in
              [uu____15243] in
            let uu____15251 =
              let uu____15252 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15252 tt in
            (uu____15238, [bb], uu____15251) in
          FStar_SMTEncoding_Util.mkForall uu____15227 in
        (uu____15226, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15219 in
    let uu____15273 =
      let uu____15276 =
        let uu____15277 =
          let uu____15284 =
            let uu____15285 =
              let uu____15296 =
                let uu____15297 =
                  let uu____15302 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15302) in
                FStar_SMTEncoding_Util.mkImp uu____15297 in
              ([[typing_pred]], [xx], uu____15296) in
            mkForall_fuel uu____15285 in
          (uu____15284, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15277 in
      [uu____15276] in
    uu____15218 :: uu____15273 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15355 =
      let uu____15356 =
        let uu____15363 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15363, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15356 in
    [uu____15355] in
  let mk_and_interp env conj uu____15375 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15400 =
      let uu____15401 =
        let uu____15408 =
          let uu____15409 =
            let uu____15420 =
              let uu____15421 =
                let uu____15426 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15426, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15421 in
            ([[l_and_a_b]], [aa; bb], uu____15420) in
          FStar_SMTEncoding_Util.mkForall uu____15409 in
        (uu____15408, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15401 in
    [uu____15400] in
  let mk_or_interp env disj uu____15464 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15489 =
      let uu____15490 =
        let uu____15497 =
          let uu____15498 =
            let uu____15509 =
              let uu____15510 =
                let uu____15515 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15515, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15510 in
            ([[l_or_a_b]], [aa; bb], uu____15509) in
          FStar_SMTEncoding_Util.mkForall uu____15498 in
        (uu____15497, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15490 in
    [uu____15489] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15578 =
      let uu____15579 =
        let uu____15586 =
          let uu____15587 =
            let uu____15598 =
              let uu____15599 =
                let uu____15604 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15604, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15599 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15598) in
          FStar_SMTEncoding_Util.mkForall uu____15587 in
        (uu____15586, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15579 in
    [uu____15578] in
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
    let uu____15677 =
      let uu____15678 =
        let uu____15685 =
          let uu____15686 =
            let uu____15697 =
              let uu____15698 =
                let uu____15703 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15703, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15698 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15697) in
          FStar_SMTEncoding_Util.mkForall uu____15686 in
        (uu____15685, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15678 in
    [uu____15677] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15774 =
      let uu____15775 =
        let uu____15782 =
          let uu____15783 =
            let uu____15794 =
              let uu____15795 =
                let uu____15800 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15800, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15795 in
            ([[l_imp_a_b]], [aa; bb], uu____15794) in
          FStar_SMTEncoding_Util.mkForall uu____15783 in
        (uu____15782, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15775 in
    [uu____15774] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15863 =
      let uu____15864 =
        let uu____15871 =
          let uu____15872 =
            let uu____15883 =
              let uu____15884 =
                let uu____15889 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15889, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15884 in
            ([[l_iff_a_b]], [aa; bb], uu____15883) in
          FStar_SMTEncoding_Util.mkForall uu____15872 in
        (uu____15871, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15864 in
    [uu____15863] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15941 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15941 in
    let uu____15944 =
      let uu____15945 =
        let uu____15952 =
          let uu____15953 =
            let uu____15964 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15964) in
          FStar_SMTEncoding_Util.mkForall uu____15953 in
        (uu____15952, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15945 in
    [uu____15944] in
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
      let uu____16024 =
        let uu____16031 =
          let uu____16034 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16034] in
        ("Valid", uu____16031) in
      FStar_SMTEncoding_Util.mkApp uu____16024 in
    let uu____16037 =
      let uu____16038 =
        let uu____16045 =
          let uu____16046 =
            let uu____16057 =
              let uu____16058 =
                let uu____16063 =
                  let uu____16064 =
                    let uu____16075 =
                      let uu____16080 =
                        let uu____16083 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16083] in
                      [uu____16080] in
                    let uu____16088 =
                      let uu____16089 =
                        let uu____16094 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16094, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16089 in
                    (uu____16075, [xx1], uu____16088) in
                  FStar_SMTEncoding_Util.mkForall uu____16064 in
                (uu____16063, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16058 in
            ([[l_forall_a_b]], [aa; bb], uu____16057) in
          FStar_SMTEncoding_Util.mkForall uu____16046 in
        (uu____16045, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16038 in
    [uu____16037] in
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
      let uu____16176 =
        let uu____16183 =
          let uu____16186 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16186] in
        ("Valid", uu____16183) in
      FStar_SMTEncoding_Util.mkApp uu____16176 in
    let uu____16189 =
      let uu____16190 =
        let uu____16197 =
          let uu____16198 =
            let uu____16209 =
              let uu____16210 =
                let uu____16215 =
                  let uu____16216 =
                    let uu____16227 =
                      let uu____16232 =
                        let uu____16235 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16235] in
                      [uu____16232] in
                    let uu____16240 =
                      let uu____16241 =
                        let uu____16246 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16246, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16241 in
                    (uu____16227, [xx1], uu____16240) in
                  FStar_SMTEncoding_Util.mkExists uu____16216 in
                (uu____16215, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16210 in
            ([[l_exists_a_b]], [aa; bb], uu____16209) in
          FStar_SMTEncoding_Util.mkForall uu____16198 in
        (uu____16197, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16190 in
    [uu____16189] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16306 =
      let uu____16307 =
        let uu____16314 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16315 = varops.mk_unique "typing_range_const" in
        (uu____16314, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16315) in
      FStar_SMTEncoding_Util.mkAssume uu____16307 in
    [uu____16306] in
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
        let uu____16349 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16349 x1 t in
      let uu____16350 =
        let uu____16361 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16361) in
      FStar_SMTEncoding_Util.mkForall uu____16350 in
    let uu____16384 =
      let uu____16385 =
        let uu____16392 =
          let uu____16393 =
            let uu____16404 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16404) in
          FStar_SMTEncoding_Util.mkForall uu____16393 in
        (uu____16392,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16385 in
    [uu____16384] in
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
          let uu____16728 =
            FStar_Util.find_opt
              (fun uu____16754  ->
                 match uu____16754 with
                 | (l,uu____16766) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16728 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16791,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16830 = encode_function_type_as_formula t env in
        match uu____16830 with
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
              let uu____16876 =
                ((let uu____16879 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16879) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16876
              then
                let uu____16886 = new_term_constant_and_tok_from_lid env lid in
                match uu____16886 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16905 =
                        let uu____16906 = FStar_Syntax_Subst.compress t_norm in
                        uu____16906.FStar_Syntax_Syntax.n in
                      match uu____16905 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16912) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16942  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16947 -> [] in
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
                (let uu____16961 = prims.is lid in
                 if uu____16961
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16969 = prims.mk lid vname in
                   match uu____16969 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16993 =
                      let uu____17004 = curried_arrow_formals_comp t_norm in
                      match uu____17004 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17022 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17022
                            then
                              let uu____17023 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___165_17026 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___165_17026.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___165_17026.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___165_17026.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___165_17026.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___165_17026.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___165_17026.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___165_17026.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___165_17026.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___165_17026.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___165_17026.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___165_17026.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___165_17026.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___165_17026.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___165_17026.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___165_17026.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___165_17026.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___165_17026.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___165_17026.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___165_17026.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___165_17026.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___165_17026.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___165_17026.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___165_17026.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___165_17026.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___165_17026.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___165_17026.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___165_17026.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___165_17026.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___165_17026.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___165_17026.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___165_17026.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___165_17026.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17023
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17038 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17038)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16993 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17083 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17083 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17104 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___137_17146  ->
                                       match uu___137_17146 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17150 =
                                             FStar_Util.prefix vars in
                                           (match uu____17150 with
                                            | (uu____17171,(xxsym,uu____17173))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17191 =
                                                  let uu____17192 =
                                                    let uu____17199 =
                                                      let uu____17200 =
                                                        let uu____17211 =
                                                          let uu____17212 =
                                                            let uu____17217 =
                                                              let uu____17218
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17218 in
                                                            (vapp,
                                                              uu____17217) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17212 in
                                                        ([[vapp]], vars,
                                                          uu____17211) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17200 in
                                                    (uu____17199,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17192 in
                                                [uu____17191])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17237 =
                                             FStar_Util.prefix vars in
                                           (match uu____17237 with
                                            | (uu____17258,(xxsym,uu____17260))
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
                                                let uu____17283 =
                                                  let uu____17284 =
                                                    let uu____17291 =
                                                      let uu____17292 =
                                                        let uu____17303 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17303) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17292 in
                                                    (uu____17291,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17284 in
                                                [uu____17283])
                                       | uu____17320 -> [])) in
                             let uu____17321 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17321 with
                              | (vars,guards,env',decls1,uu____17348) ->
                                  let uu____17361 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17370 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17370, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17372 =
                                          encode_formula p env' in
                                        (match uu____17372 with
                                         | (g,ds) ->
                                             let uu____17383 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17383,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17361 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17396 =
                                           let uu____17403 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17403) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17396 in
                                       let uu____17412 =
                                         let vname_decl =
                                           let uu____17420 =
                                             let uu____17431 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17441  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17431,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17420 in
                                         let uu____17450 =
                                           let env2 =
                                             let uu___166_17456 = env1 in
                                             {
                                               bindings =
                                                 (uu___166_17456.bindings);
                                               depth = (uu___166_17456.depth);
                                               tcenv = (uu___166_17456.tcenv);
                                               warn = (uu___166_17456.warn);
                                               cache = (uu___166_17456.cache);
                                               nolabels =
                                                 (uu___166_17456.nolabels);
                                               use_zfuel_name =
                                                 (uu___166_17456.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___166_17456.current_module_name)
                                             } in
                                           let uu____17457 =
                                             let uu____17458 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17458 in
                                           if uu____17457
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17450 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17473::uu____17474 ->
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
                                                     let uu____17514 =
                                                       let uu____17525 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17525) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17514 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17552 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17555 =
                                               match formals with
                                               | [] ->
                                                   let uu____17572 =
                                                     let uu____17573 =
                                                       let uu____17576 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17576 in
                                                     push_free_var env1 lid
                                                       vname uu____17573 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17572)
                                               | uu____17581 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17588 =
                                                       let uu____17595 =
                                                         let uu____17596 =
                                                           let uu____17607 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17607) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17596 in
                                                       (uu____17595,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17588 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17555 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17412 with
                                        | (decls2,env2) ->
                                            let uu____17650 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17658 =
                                                encode_term res_t1 env' in
                                              match uu____17658 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17671 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17671, decls) in
                                            (match uu____17650 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17682 =
                                                     let uu____17689 =
                                                       let uu____17690 =
                                                         let uu____17701 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17701) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17690 in
                                                     (uu____17689,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17682 in
                                                 let freshness =
                                                   let uu____17717 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17717
                                                   then
                                                     let uu____17722 =
                                                       let uu____17723 =
                                                         let uu____17734 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17745 =
                                                           varops.next_id () in
                                                         (vname, uu____17734,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17745) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17723 in
                                                     let uu____17748 =
                                                       let uu____17751 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17751] in
                                                     uu____17722 ::
                                                       uu____17748
                                                   else [] in
                                                 let g =
                                                   let uu____17756 =
                                                     let uu____17759 =
                                                       let uu____17762 =
                                                         let uu____17765 =
                                                           let uu____17768 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17768 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17765 in
                                                       FStar_List.append
                                                         decls3 uu____17762 in
                                                     FStar_List.append decls2
                                                       uu____17759 in
                                                   FStar_List.append decls11
                                                     uu____17756 in
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
          let uu____17803 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17803 with
          | FStar_Pervasives_Native.None  ->
              let uu____17840 = encode_free_var false env x t t_norm [] in
              (match uu____17840 with
               | (decls,env1) ->
                   let uu____17867 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17867 with
                    | (n1,x',uu____17894) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17915) ->
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
            let uu____17975 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17975 with
            | (decls,env1) ->
                let uu____17994 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17994
                then
                  let uu____18001 =
                    let uu____18004 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18004 in
                  (uu____18001, env1)
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
             (fun uu____18059  ->
                fun lb  ->
                  match uu____18059 with
                  | (decls,env1) ->
                      let uu____18079 =
                        let uu____18086 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18086
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18079 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18108 = FStar_Syntax_Util.head_and_args t in
    match uu____18108 with
    | (hd1,args) ->
        let uu____18145 =
          let uu____18146 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18146.FStar_Syntax_Syntax.n in
        (match uu____18145 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18150,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18169 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18194  ->
      fun quals  ->
        match uu____18194 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18270 = FStar_Util.first_N nbinders formals in
              match uu____18270 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18351  ->
                         fun uu____18352  ->
                           match (uu____18351, uu____18352) with
                           | ((formal,uu____18370),(binder,uu____18372)) ->
                               let uu____18381 =
                                 let uu____18388 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18388) in
                               FStar_Syntax_Syntax.NT uu____18381) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18396 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18427  ->
                              match uu____18427 with
                              | (x,i) ->
                                  let uu____18438 =
                                    let uu___167_18439 = x in
                                    let uu____18440 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___167_18439.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___167_18439.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18440
                                    } in
                                  (uu____18438, i))) in
                    FStar_All.pipe_right uu____18396
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18458 =
                      let uu____18459 = FStar_Syntax_Subst.compress body in
                      let uu____18460 =
                        let uu____18461 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18461 in
                      FStar_Syntax_Syntax.extend_app_n uu____18459
                        uu____18460 in
                    uu____18458 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18522 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18522
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___168_18525 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___168_18525.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___168_18525.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___168_18525.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___168_18525.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___168_18525.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___168_18525.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___168_18525.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___168_18525.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___168_18525.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___168_18525.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___168_18525.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___168_18525.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___168_18525.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___168_18525.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___168_18525.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___168_18525.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___168_18525.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___168_18525.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___168_18525.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___168_18525.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___168_18525.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___168_18525.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___168_18525.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___168_18525.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___168_18525.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___168_18525.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___168_18525.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___168_18525.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___168_18525.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___168_18525.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___168_18525.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___168_18525.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18558 = FStar_Syntax_Util.abs_formals e in
                match uu____18558 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18622::uu____18623 ->
                         let uu____18638 =
                           let uu____18639 =
                             let uu____18642 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18642 in
                           uu____18639.FStar_Syntax_Syntax.n in
                         (match uu____18638 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18685 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18685 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18727 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18727
                                   then
                                     let uu____18762 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18762 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18856  ->
                                                   fun uu____18857  ->
                                                     match (uu____18856,
                                                             uu____18857)
                                                     with
                                                     | ((x,uu____18875),
                                                        (b,uu____18877)) ->
                                                         let uu____18886 =
                                                           let uu____18893 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18893) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18886)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18895 =
                                            let uu____18916 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18916) in
                                          (uu____18895, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18984 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18984 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19073) ->
                              let uu____19078 =
                                let uu____19099 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19099 in
                              (uu____19078, true)
                          | uu____19164 when Prims.op_Negation norm1 ->
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
                          | uu____19166 ->
                              let uu____19167 =
                                let uu____19168 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19169 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19168
                                  uu____19169 in
                              failwith uu____19167)
                     | uu____19194 ->
                         let uu____19195 =
                           let uu____19196 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19196.FStar_Syntax_Syntax.n in
                         (match uu____19195 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19241 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19241 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19273 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19273 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19356 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19412 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19412
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19424 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19518  ->
                            fun lb  ->
                              match uu____19518 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19613 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19613
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19616 =
                                      let uu____19631 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19631
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19616 with
                                    | (tok,decl,env2) ->
                                        let uu____19677 =
                                          let uu____19690 =
                                            let uu____19701 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19701, tok) in
                                          uu____19690 :: toks in
                                        (uu____19677, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19424 with
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
                        | uu____19884 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19892 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19892 vars)
                            else
                              (let uu____19894 =
                                 let uu____19901 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19901) in
                               FStar_SMTEncoding_Util.mkApp uu____19894) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19983;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19985;
                             FStar_Syntax_Syntax.lbeff = uu____19986;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20049 =
                              let uu____20056 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20056 with
                              | (tcenv',uu____20074,e_t) ->
                                  let uu____20080 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20091 -> failwith "Impossible" in
                                  (match uu____20080 with
                                   | (e1,t_norm1) ->
                                       ((let uu___171_20107 = env2 in
                                         {
                                           bindings =
                                             (uu___171_20107.bindings);
                                           depth = (uu___171_20107.depth);
                                           tcenv = tcenv';
                                           warn = (uu___171_20107.warn);
                                           cache = (uu___171_20107.cache);
                                           nolabels =
                                             (uu___171_20107.nolabels);
                                           use_zfuel_name =
                                             (uu___171_20107.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___171_20107.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___171_20107.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20049 with
                             | (env',e1,t_norm1) ->
                                 let uu____20117 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20117 with
                                  | ((binders,body,uu____20138,uu____20139),curry)
                                      ->
                                      ((let uu____20150 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20150
                                        then
                                          let uu____20151 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20152 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20151 uu____20152
                                        else ());
                                       (let uu____20154 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20154 with
                                        | (vars,guards,env'1,binder_decls,uu____20181)
                                            ->
                                            let body1 =
                                              let uu____20195 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20195
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20198 =
                                              let uu____20207 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20207
                                              then
                                                let uu____20218 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20219 =
                                                  encode_formula body1 env'1 in
                                                (uu____20218, uu____20219)
                                              else
                                                (let uu____20229 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20229)) in
                                            (match uu____20198 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20252 =
                                                     let uu____20259 =
                                                       let uu____20260 =
                                                         let uu____20271 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20271) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20260 in
                                                     let uu____20282 =
                                                       let uu____20285 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20285 in
                                                     (uu____20259,
                                                       uu____20282,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20252 in
                                                 let uu____20288 =
                                                   let uu____20291 =
                                                     let uu____20294 =
                                                       let uu____20297 =
                                                         let uu____20300 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20300 in
                                                       FStar_List.append
                                                         decls2 uu____20297 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20294 in
                                                   FStar_List.append decls1
                                                     uu____20291 in
                                                 (uu____20288, env2))))))
                        | uu____20305 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20390 = varops.fresh "fuel" in
                          (uu____20390, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20393 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20481  ->
                                  fun uu____20482  ->
                                    match (uu____20481, uu____20482) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20630 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20630 in
                                        let gtok =
                                          let uu____20632 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20632 in
                                        let env4 =
                                          let uu____20634 =
                                            let uu____20637 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20637 in
                                          push_free_var env3 flid gtok
                                            uu____20634 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20393 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20793 t_norm
                              uu____20795 =
                              match (uu____20793, uu____20795) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20839;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20840;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20868 =
                                    let uu____20875 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20875 with
                                    | (tcenv',uu____20897,e_t) ->
                                        let uu____20903 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20914 ->
                                              failwith "Impossible" in
                                        (match uu____20903 with
                                         | (e1,t_norm1) ->
                                             ((let uu___172_20930 = env3 in
                                               {
                                                 bindings =
                                                   (uu___172_20930.bindings);
                                                 depth =
                                                   (uu___172_20930.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___172_20930.warn);
                                                 cache =
                                                   (uu___172_20930.cache);
                                                 nolabels =
                                                   (uu___172_20930.nolabels);
                                                 use_zfuel_name =
                                                   (uu___172_20930.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___172_20930.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___172_20930.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20868 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20945 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20945
                                         then
                                           let uu____20946 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20947 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20948 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20946 uu____20947
                                             uu____20948
                                         else ());
                                        (let uu____20950 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20950 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20987 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20987
                                               then
                                                 let uu____20988 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20989 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20990 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20991 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20988 uu____20989
                                                   uu____20990 uu____20991
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20995 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20995 with
                                               | (vars,guards,env'1,binder_decls,uu____21026)
                                                   ->
                                                   let decl_g =
                                                     let uu____21040 =
                                                       let uu____21051 =
                                                         let uu____21054 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21054 in
                                                       (g, uu____21051,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21040 in
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
                                                     let uu____21079 =
                                                       let uu____21086 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21086) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21079 in
                                                   let gsapp =
                                                     let uu____21096 =
                                                       let uu____21103 =
                                                         let uu____21106 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21106 ::
                                                           vars_tm in
                                                       (g, uu____21103) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21096 in
                                                   let gmax =
                                                     let uu____21112 =
                                                       let uu____21119 =
                                                         let uu____21122 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21122 ::
                                                           vars_tm in
                                                       (g, uu____21119) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21112 in
                                                   let body1 =
                                                     let uu____21128 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21128
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21130 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21130 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21148 =
                                                            let uu____21155 =
                                                              let uu____21156
                                                                =
                                                                let uu____21171
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
                                                                  uu____21171) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21156 in
                                                            let uu____21192 =
                                                              let uu____21195
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21195 in
                                                            (uu____21155,
                                                              uu____21192,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21148 in
                                                        let eqn_f =
                                                          let uu____21199 =
                                                            let uu____21206 =
                                                              let uu____21207
                                                                =
                                                                let uu____21218
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21218) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21207 in
                                                            (uu____21206,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21199 in
                                                        let eqn_g' =
                                                          let uu____21232 =
                                                            let uu____21239 =
                                                              let uu____21240
                                                                =
                                                                let uu____21251
                                                                  =
                                                                  let uu____21252
                                                                    =
                                                                    let uu____21257
                                                                    =
                                                                    let uu____21258
                                                                    =
                                                                    let uu____21265
                                                                    =
                                                                    let uu____21268
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21268
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21265) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21258 in
                                                                    (gsapp,
                                                                    uu____21257) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21252 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21251) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21240 in
                                                            (uu____21239,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21232 in
                                                        let uu____21291 =
                                                          let uu____21300 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21300
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21329)
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
                                                                  let uu____21354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21354
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21359
                                                                  =
                                                                  let uu____21366
                                                                    =
                                                                    let uu____21367
                                                                    =
                                                                    let uu____21378
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21378) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21367 in
                                                                  (uu____21366,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21359 in
                                                              let uu____21399
                                                                =
                                                                let uu____21406
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21406
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21419
                                                                    =
                                                                    let uu____21422
                                                                    =
                                                                    let uu____21423
                                                                    =
                                                                    let uu____21430
                                                                    =
                                                                    let uu____21431
                                                                    =
                                                                    let uu____21442
                                                                    =
                                                                    let uu____21443
                                                                    =
                                                                    let uu____21448
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21448,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21443 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21442) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21431 in
                                                                    (uu____21430,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21423 in
                                                                    [uu____21422] in
                                                                    (d3,
                                                                    uu____21419) in
                                                              (match uu____21399
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21291
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
                            let uu____21513 =
                              let uu____21526 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21605  ->
                                   fun uu____21606  ->
                                     match (uu____21605, uu____21606) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21761 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21761 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21526 in
                            (match uu____21513 with
                             | (decls2,eqns,env01) ->
                                 let uu____21834 =
                                   let isDeclFun uu___138_21846 =
                                     match uu___138_21846 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21847 -> true
                                     | uu____21858 -> false in
                                   let uu____21859 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21859
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21834 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21899 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___139_21903  ->
                                 match uu___139_21903 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21904 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21910 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21910))) in
                      if uu____21899
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
                   let uu____21962 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21962
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
        let uu____22011 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22011 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22015 = encode_sigelt' env se in
      match uu____22015 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22031 =
                  let uu____22032 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22032 in
                [uu____22031]
            | uu____22033 ->
                let uu____22034 =
                  let uu____22037 =
                    let uu____22038 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22038 in
                  uu____22037 :: g in
                let uu____22039 =
                  let uu____22042 =
                    let uu____22043 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22043 in
                  [uu____22042] in
                FStar_List.append uu____22034 uu____22039 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22056 =
          let uu____22057 = FStar_Syntax_Subst.compress t in
          uu____22057.FStar_Syntax_Syntax.n in
        match uu____22056 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22061)) -> s = "opaque_to_smt"
        | uu____22062 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22067 =
          let uu____22068 = FStar_Syntax_Subst.compress t in
          uu____22068.FStar_Syntax_Syntax.n in
        match uu____22067 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22072)) -> s = "uninterpreted_by_smt"
        | uu____22073 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22078 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22083 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22086 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22089 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22104 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22108 =
            let uu____22109 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22109 Prims.op_Negation in
          if uu____22108
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22135 ->
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
               let uu____22155 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22155 with
               | (aname,atok,env2) ->
                   let uu____22171 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22171 with
                    | (formals,uu____22189) ->
                        let uu____22202 =
                          let uu____22207 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22207 env2 in
                        (match uu____22202 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22219 =
                                 let uu____22220 =
                                   let uu____22231 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22247  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22231,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22220 in
                               [uu____22219;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22260 =
                               let aux uu____22312 uu____22313 =
                                 match (uu____22312, uu____22313) with
                                 | ((bv,uu____22365),(env3,acc_sorts,acc)) ->
                                     let uu____22403 = gen_term_var env3 bv in
                                     (match uu____22403 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22260 with
                              | (uu____22475,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22498 =
                                      let uu____22505 =
                                        let uu____22506 =
                                          let uu____22517 =
                                            let uu____22518 =
                                              let uu____22523 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22523) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22518 in
                                          ([[app]], xs_sorts, uu____22517) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22506 in
                                      (uu____22505,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22498 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22543 =
                                      let uu____22550 =
                                        let uu____22551 =
                                          let uu____22562 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22562) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22551 in
                                      (uu____22550,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22543 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22581 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22581 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22609,uu____22610)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22611 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22611 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22628,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22634 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___140_22638  ->
                      match uu___140_22638 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22639 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22644 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22645 -> false)) in
            Prims.op_Negation uu____22634 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22654 =
               let uu____22661 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22661 env fv t quals in
             match uu____22654 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22676 =
                   let uu____22679 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22679 in
                 (uu____22676, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22687 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22687 with
           | (uu____22696,f1) ->
               let uu____22698 = encode_formula f1 env in
               (match uu____22698 with
                | (f2,decls) ->
                    let g =
                      let uu____22712 =
                        let uu____22713 =
                          let uu____22720 =
                            let uu____22723 =
                              let uu____22724 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22724 in
                            FStar_Pervasives_Native.Some uu____22723 in
                          let uu____22725 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22720, uu____22725) in
                        FStar_SMTEncoding_Util.mkAssume uu____22713 in
                      [uu____22712] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22731) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22743 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22761 =
                       let uu____22764 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22764.FStar_Syntax_Syntax.fv_name in
                     uu____22761.FStar_Syntax_Syntax.v in
                   let uu____22765 =
                     let uu____22766 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22766 in
                   if uu____22765
                   then
                     let val_decl =
                       let uu___175_22794 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___175_22794.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___175_22794.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___175_22794.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22799 = encode_sigelt' env1 val_decl in
                     match uu____22799 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22743 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22827,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22829;
                          FStar_Syntax_Syntax.lbtyp = uu____22830;
                          FStar_Syntax_Syntax.lbeff = uu____22831;
                          FStar_Syntax_Syntax.lbdef = uu____22832;_}::[]),uu____22833)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22852 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22852 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22881 =
                   let uu____22884 =
                     let uu____22885 =
                       let uu____22892 =
                         let uu____22893 =
                           let uu____22904 =
                             let uu____22905 =
                               let uu____22910 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22910) in
                             FStar_SMTEncoding_Util.mkEq uu____22905 in
                           ([[b2t_x]], [xx], uu____22904) in
                         FStar_SMTEncoding_Util.mkForall uu____22893 in
                       (uu____22892,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22885 in
                   [uu____22884] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22881 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22943,uu____22944) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___141_22953  ->
                  match uu___141_22953 with
                  | FStar_Syntax_Syntax.Discriminator uu____22954 -> true
                  | uu____22955 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22958,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22969 =
                     let uu____22970 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22970.FStar_Ident.idText in
                   uu____22969 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___142_22974  ->
                     match uu___142_22974 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22975 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22979) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___143_22996  ->
                  match uu___143_22996 with
                  | FStar_Syntax_Syntax.Projector uu____22997 -> true
                  | uu____23002 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23005 = try_lookup_free_var env l in
          (match uu____23005 with
           | FStar_Pervasives_Native.Some uu____23012 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___176_23016 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___176_23016.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___176_23016.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___176_23016.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23023) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23041) ->
          let uu____23050 = encode_sigelts env ses in
          (match uu____23050 with
           | (g,env1) ->
               let uu____23067 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___144_23090  ->
                         match uu___144_23090 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23091;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23092;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23093;_}
                             -> false
                         | uu____23096 -> true)) in
               (match uu____23067 with
                | (g',inversions) ->
                    let uu____23111 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___145_23132  ->
                              match uu___145_23132 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23133 ->
                                  true
                              | uu____23144 -> false)) in
                    (match uu____23111 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23162,tps,k,uu____23165,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___146_23182  ->
                    match uu___146_23182 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23183 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23192 = c in
              match uu____23192 with
              | (name,args,uu____23197,uu____23198,uu____23199) ->
                  let uu____23204 =
                    let uu____23205 =
                      let uu____23216 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23233  ->
                                match uu____23233 with
                                | (uu____23240,sort,uu____23242) -> sort)) in
                      (name, uu____23216, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23205 in
                  [uu____23204]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23269 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23275 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23275 FStar_Option.isNone)) in
            if uu____23269
            then []
            else
              (let uu____23307 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23307 with
               | (xxsym,xx) ->
                   let uu____23316 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23355  ->
                             fun l  ->
                               match uu____23355 with
                               | (out,decls) ->
                                   let uu____23375 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23375 with
                                    | (uu____23386,data_t) ->
                                        let uu____23388 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23388 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23434 =
                                                 let uu____23435 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23435.FStar_Syntax_Syntax.n in
                                               match uu____23434 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23446,indices) ->
                                                   indices
                                               | uu____23468 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23492  ->
                                                         match uu____23492
                                                         with
                                                         | (x,uu____23498) ->
                                                             let uu____23499
                                                               =
                                                               let uu____23500
                                                                 =
                                                                 let uu____23507
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23507,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23500 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23499)
                                                    env) in
                                             let uu____23510 =
                                               encode_args indices env1 in
                                             (match uu____23510 with
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
                                                      let uu____23536 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23552
                                                                 =
                                                                 let uu____23557
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23557,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23552)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23536
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23560 =
                                                      let uu____23561 =
                                                        let uu____23566 =
                                                          let uu____23567 =
                                                            let uu____23572 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23572,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23567 in
                                                        (out, uu____23566) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23561 in
                                                    (uu____23560,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23316 with
                    | (data_ax,decls) ->
                        let uu____23585 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23585 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23596 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23596 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23600 =
                                 let uu____23607 =
                                   let uu____23608 =
                                     let uu____23619 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23634 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23619,
                                       uu____23634) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23608 in
                                 let uu____23649 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23607,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23649) in
                               FStar_SMTEncoding_Util.mkAssume uu____23600 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23652 =
            let uu____23665 =
              let uu____23666 = FStar_Syntax_Subst.compress k in
              uu____23666.FStar_Syntax_Syntax.n in
            match uu____23665 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23711 -> (tps, k) in
          (match uu____23652 with
           | (formals,res) ->
               let uu____23734 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23734 with
                | (formals1,res1) ->
                    let uu____23745 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23745 with
                     | (vars,guards,env',binder_decls,uu____23770) ->
                         let uu____23783 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23783 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23802 =
                                  let uu____23809 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23809) in
                                FStar_SMTEncoding_Util.mkApp uu____23802 in
                              let uu____23818 =
                                let tname_decl =
                                  let uu____23828 =
                                    let uu____23829 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23861  ->
                                              match uu____23861 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23874 = varops.next_id () in
                                    (tname, uu____23829,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23874, false) in
                                  constructor_or_logic_type_decl uu____23828 in
                                let uu____23883 =
                                  match vars with
                                  | [] ->
                                      let uu____23896 =
                                        let uu____23897 =
                                          let uu____23900 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23900 in
                                        push_free_var env1 t tname
                                          uu____23897 in
                                      ([], uu____23896)
                                  | uu____23907 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23916 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23916 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23930 =
                                          let uu____23937 =
                                            let uu____23938 =
                                              let uu____23953 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23953) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23938 in
                                          (uu____23937,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23930 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23883 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23818 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23993 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23993 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24011 =
                                               let uu____24012 =
                                                 let uu____24019 =
                                                   let uu____24020 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24020 in
                                                 (uu____24019,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24012 in
                                             [uu____24011]
                                           else [] in
                                         let uu____24024 =
                                           let uu____24027 =
                                             let uu____24030 =
                                               let uu____24031 =
                                                 let uu____24038 =
                                                   let uu____24039 =
                                                     let uu____24050 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24050) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24039 in
                                                 (uu____24038,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24031 in
                                             [uu____24030] in
                                           FStar_List.append karr uu____24027 in
                                         FStar_List.append decls1 uu____24024 in
                                   let aux =
                                     let uu____24066 =
                                       let uu____24069 =
                                         inversion_axioms tapp vars in
                                       let uu____24072 =
                                         let uu____24075 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24075] in
                                       FStar_List.append uu____24069
                                         uu____24072 in
                                     FStar_List.append kindingAx uu____24066 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24082,uu____24083,uu____24084,uu____24085,uu____24086)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24094,t,uu____24096,n_tps,uu____24098) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24106 = new_term_constant_and_tok_from_lid env d in
          (match uu____24106 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24123 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24123 with
                | (formals,t_res) ->
                    let uu____24158 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24158 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24172 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24172 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24242 =
                                            mk_term_projector_name d x in
                                          (uu____24242,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24244 =
                                  let uu____24263 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24263, true) in
                                FStar_All.pipe_right uu____24244
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
                              let uu____24302 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24302 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24314::uu____24315 ->
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
                                         let uu____24360 =
                                           let uu____24371 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24371) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24360
                                     | uu____24396 -> tok_typing in
                                   let uu____24405 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24405 with
                                    | (vars',guards',env'',decls_formals,uu____24430)
                                        ->
                                        let uu____24443 =
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
                                        (match uu____24443 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24474 ->
                                                   let uu____24481 =
                                                     let uu____24482 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24482 in
                                                   [uu____24481] in
                                             let encode_elim uu____24492 =
                                               let uu____24493 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24493 with
                                               | (head1,args) ->
                                                   let uu____24536 =
                                                     let uu____24537 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24537.FStar_Syntax_Syntax.n in
                                                   (match uu____24536 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24547;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24548;_},uu____24549)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24555 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24555
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
                                                                 | uu____24598
                                                                    ->
                                                                    let uu____24599
                                                                    =
                                                                    let uu____24600
                                                                    =
                                                                    let uu____24605
                                                                    =
                                                                    let uu____24606
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24606 in
                                                                    (uu____24605,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24600 in
                                                                    FStar_Exn.raise
                                                                    uu____24599 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24622
                                                                    =
                                                                    let uu____24623
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24623 in
                                                                    if
                                                                    uu____24622
                                                                    then
                                                                    let uu____24636
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24636]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24638
                                                               =
                                                               let uu____24651
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24701
                                                                     ->
                                                                    fun
                                                                    uu____24702
                                                                     ->
                                                                    match 
                                                                    (uu____24701,
                                                                    uu____24702)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24797
                                                                    =
                                                                    let uu____24804
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24804 in
                                                                    (match uu____24797
                                                                    with
                                                                    | 
                                                                    (uu____24817,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24825
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24825
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24827
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24827
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
                                                                 uu____24651 in
                                                             (match uu____24638
                                                              with
                                                              | (uu____24842,arg_vars,elim_eqns_or_guards,uu____24845)
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
                                                                    let uu____24875
                                                                    =
                                                                    let uu____24882
                                                                    =
                                                                    let uu____24883
                                                                    =
                                                                    let uu____24894
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24905
                                                                    =
                                                                    let uu____24906
                                                                    =
                                                                    let uu____24911
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24911) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24906 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24894,
                                                                    uu____24905) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24883 in
                                                                    (uu____24882,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24875 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24934
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24934,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24936
                                                                    =
                                                                    let uu____24943
                                                                    =
                                                                    let uu____24944
                                                                    =
                                                                    let uu____24955
                                                                    =
                                                                    let uu____24960
                                                                    =
                                                                    let uu____24963
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24963] in
                                                                    [uu____24960] in
                                                                    let uu____24968
                                                                    =
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24974
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24975
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24974,
                                                                    uu____24975) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24969 in
                                                                    (uu____24955,
                                                                    [x],
                                                                    uu____24968) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24944 in
                                                                    let uu____24994
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24943,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24994) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24936
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25001
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
                                                                    (let uu____25029
                                                                    =
                                                                    let uu____25030
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25030
                                                                    dapp1 in
                                                                    [uu____25029]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25001
                                                                    FStar_List.flatten in
                                                                    let uu____25037
                                                                    =
                                                                    let uu____25044
                                                                    =
                                                                    let uu____25045
                                                                    =
                                                                    let uu____25056
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25067
                                                                    =
                                                                    let uu____25068
                                                                    =
                                                                    let uu____25073
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25073) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25068 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25056,
                                                                    uu____25067) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25045 in
                                                                    (uu____25044,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25037) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25094 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25094
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
                                                                 | uu____25137
                                                                    ->
                                                                    let uu____25138
                                                                    =
                                                                    let uu____25139
                                                                    =
                                                                    let uu____25144
                                                                    =
                                                                    let uu____25145
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25145 in
                                                                    (uu____25144,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25139 in
                                                                    FStar_Exn.raise
                                                                    uu____25138 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25161
                                                                    =
                                                                    let uu____25162
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25162 in
                                                                    if
                                                                    uu____25161
                                                                    then
                                                                    let uu____25175
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25175]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25177
                                                               =
                                                               let uu____25190
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25240
                                                                     ->
                                                                    fun
                                                                    uu____25241
                                                                     ->
                                                                    match 
                                                                    (uu____25240,
                                                                    uu____25241)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25336
                                                                    =
                                                                    let uu____25343
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25343 in
                                                                    (match uu____25336
                                                                    with
                                                                    | 
                                                                    (uu____25356,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25364
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25364
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25366
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25366
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
                                                                 uu____25190 in
                                                             (match uu____25177
                                                              with
                                                              | (uu____25381,arg_vars,elim_eqns_or_guards,uu____25384)
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
                                                                    let uu____25414
                                                                    =
                                                                    let uu____25421
                                                                    =
                                                                    let uu____25422
                                                                    =
                                                                    let uu____25433
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25444
                                                                    =
                                                                    let uu____25445
                                                                    =
                                                                    let uu____25450
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25450) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25445 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25433,
                                                                    uu____25444) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25422 in
                                                                    (uu____25421,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25414 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25473
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25473,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25475
                                                                    =
                                                                    let uu____25482
                                                                    =
                                                                    let uu____25483
                                                                    =
                                                                    let uu____25494
                                                                    =
                                                                    let uu____25499
                                                                    =
                                                                    let uu____25502
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25502] in
                                                                    [uu____25499] in
                                                                    let uu____25507
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25513,
                                                                    uu____25514) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25508 in
                                                                    (uu____25494,
                                                                    [x],
                                                                    uu____25507) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25483 in
                                                                    let uu____25533
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25482,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25533) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25475
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25540
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
                                                                    (let uu____25568
                                                                    =
                                                                    let uu____25569
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25569
                                                                    dapp1 in
                                                                    [uu____25568]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25540
                                                                    FStar_List.flatten in
                                                                    let uu____25576
                                                                    =
                                                                    let uu____25583
                                                                    =
                                                                    let uu____25584
                                                                    =
                                                                    let uu____25595
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25606
                                                                    =
                                                                    let uu____25607
                                                                    =
                                                                    let uu____25612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25612) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25607 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25595,
                                                                    uu____25606) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25584 in
                                                                    (uu____25583,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25576) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25631 ->
                                                        ((let uu____25633 =
                                                            let uu____25634 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25635 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25634
                                                              uu____25635 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25633);
                                                         ([], []))) in
                                             let uu____25640 = encode_elim () in
                                             (match uu____25640 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25660 =
                                                      let uu____25663 =
                                                        let uu____25666 =
                                                          let uu____25669 =
                                                            let uu____25672 =
                                                              let uu____25673
                                                                =
                                                                let uu____25684
                                                                  =
                                                                  let uu____25687
                                                                    =
                                                                    let uu____25688
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25688 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25687 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25684) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25673 in
                                                            [uu____25672] in
                                                          let uu____25693 =
                                                            let uu____25696 =
                                                              let uu____25699
                                                                =
                                                                let uu____25702
                                                                  =
                                                                  let uu____25705
                                                                    =
                                                                    let uu____25708
                                                                    =
                                                                    let uu____25711
                                                                    =
                                                                    let uu____25712
                                                                    =
                                                                    let uu____25719
                                                                    =
                                                                    let uu____25720
                                                                    =
                                                                    let uu____25731
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25731) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25720 in
                                                                    (uu____25719,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25712 in
                                                                    let uu____25744
                                                                    =
                                                                    let uu____25747
                                                                    =
                                                                    let uu____25748
                                                                    =
                                                                    let uu____25755
                                                                    =
                                                                    let uu____25756
                                                                    =
                                                                    let uu____25767
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25778
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25767,
                                                                    uu____25778) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25756 in
                                                                    (uu____25755,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25748 in
                                                                    [uu____25747] in
                                                                    uu____25711
                                                                    ::
                                                                    uu____25744 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25708 in
                                                                  FStar_List.append
                                                                    uu____25705
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25702 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25699 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25696 in
                                                          FStar_List.append
                                                            uu____25669
                                                            uu____25693 in
                                                        FStar_List.append
                                                          decls3 uu____25666 in
                                                      FStar_List.append
                                                        decls2 uu____25663 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25660 in
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
           (fun uu____25824  ->
              fun se  ->
                match uu____25824 with
                | (g,env1) ->
                    let uu____25844 = encode_sigelt env1 se in
                    (match uu____25844 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25903 =
        match uu____25903 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25935 ->
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
                 ((let uu____25941 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25941
                   then
                     let uu____25942 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25943 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25944 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25942 uu____25943 uu____25944
                   else ());
                  (let uu____25946 = encode_term t1 env1 in
                   match uu____25946 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25962 =
                         let uu____25969 =
                           let uu____25970 =
                             let uu____25971 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25971
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25970 in
                         new_term_constant_from_string env1 x uu____25969 in
                       (match uu____25962 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25987 = FStar_Options.log_queries () in
                              if uu____25987
                              then
                                let uu____25990 =
                                  let uu____25991 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25992 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25993 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25991 uu____25992 uu____25993 in
                                FStar_Pervasives_Native.Some uu____25990
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26009,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26023 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26023 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26046,se,uu____26048) ->
                 let uu____26053 = encode_sigelt env1 se in
                 (match uu____26053 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26070,se) ->
                 let uu____26076 = encode_sigelt env1 se in
                 (match uu____26076 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26093 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26093 with | (uu____26116,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26131 'Auu____26132 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26132,'Auu____26131)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26200  ->
              match uu____26200 with
              | (l,uu____26212,uu____26213) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26259  ->
              match uu____26259 with
              | (l,uu____26273,uu____26274) ->
                  let uu____26283 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26284 =
                    let uu____26287 =
                      let uu____26288 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26288 in
                    [uu____26287] in
                  uu____26283 :: uu____26284)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26310 =
      let uu____26313 =
        let uu____26314 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26317 =
          let uu____26318 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26318 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26314;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26317
        } in
      [uu____26313] in
    FStar_ST.op_Colon_Equals last_env uu____26310
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26377 = FStar_ST.op_Bang last_env in
      match uu____26377 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26431 ->
          let uu___177_26434 = e in
          let uu____26435 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___177_26434.bindings);
            depth = (uu___177_26434.depth);
            tcenv;
            warn = (uu___177_26434.warn);
            cache = (uu___177_26434.cache);
            nolabels = (uu___177_26434.nolabels);
            use_zfuel_name = (uu___177_26434.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26434.encode_non_total_function_typ);
            current_module_name = uu____26435
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26440 = FStar_ST.op_Bang last_env in
    match uu____26440 with
    | [] -> failwith "Empty env stack"
    | uu____26493::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26550  ->
    let uu____26551 = FStar_ST.op_Bang last_env in
    match uu____26551 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___178_26612 = hd1 in
          {
            bindings = (uu___178_26612.bindings);
            depth = (uu___178_26612.depth);
            tcenv = (uu___178_26612.tcenv);
            warn = (uu___178_26612.warn);
            cache = refs;
            nolabels = (uu___178_26612.nolabels);
            use_zfuel_name = (uu___178_26612.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___178_26612.encode_non_total_function_typ);
            current_module_name = (uu___178_26612.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26666  ->
    let uu____26667 = FStar_ST.op_Bang last_env in
    match uu____26667 with
    | [] -> failwith "Popping an empty stack"
    | uu____26720::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26818::uu____26819,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___179_26827 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___179_26827.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___179_26827.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___179_26827.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26828 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26845 =
        let uu____26848 =
          let uu____26849 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26849 in
        let uu____26850 = open_fact_db_tags env in uu____26848 :: uu____26850 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26845
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
      let uu____26874 = encode_sigelt env se in
      match uu____26874 with
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
        let uu____26912 = FStar_Options.log_queries () in
        if uu____26912
        then
          let uu____26915 =
            let uu____26916 =
              let uu____26917 =
                let uu____26918 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26918 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26917 in
            FStar_SMTEncoding_Term.Caption uu____26916 in
          uu____26915 :: decls
        else decls in
      let env =
        let uu____26929 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26929 tcenv in
      let uu____26930 = encode_top_level_facts env se in
      match uu____26930 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26944 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26944))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26958 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26958
       then
         let uu____26959 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26959
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26994  ->
                 fun se  ->
                   match uu____26994 with
                   | (g,env2) ->
                       let uu____27014 = encode_top_level_facts env2 se in
                       (match uu____27014 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27037 =
         encode_signature
           (let uu___180_27046 = env in
            {
              bindings = (uu___180_27046.bindings);
              depth = (uu___180_27046.depth);
              tcenv = (uu___180_27046.tcenv);
              warn = false;
              cache = (uu___180_27046.cache);
              nolabels = (uu___180_27046.nolabels);
              use_zfuel_name = (uu___180_27046.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___180_27046.encode_non_total_function_typ);
              current_module_name = (uu___180_27046.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27037 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27063 = FStar_Options.log_queries () in
             if uu____27063
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___181_27071 = env1 in
               {
                 bindings = (uu___181_27071.bindings);
                 depth = (uu___181_27071.depth);
                 tcenv = (uu___181_27071.tcenv);
                 warn = true;
                 cache = (uu___181_27071.cache);
                 nolabels = (uu___181_27071.nolabels);
                 use_zfuel_name = (uu___181_27071.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___181_27071.encode_non_total_function_typ);
                 current_module_name = (uu___181_27071.current_module_name)
               });
            (let uu____27073 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27073
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
        (let uu____27128 =
           let uu____27129 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27129.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27128);
        (let env =
           let uu____27131 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27131 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27143 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27178 = aux rest in
                 (match uu____27178 with
                  | (out,rest1) ->
                      let t =
                        let uu____27208 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27208 with
                        | FStar_Pervasives_Native.Some uu____27213 ->
                            let uu____27214 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27214
                              x.FStar_Syntax_Syntax.sort
                        | uu____27215 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27219 =
                        let uu____27222 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___182_27225 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___182_27225.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___182_27225.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27222 :: out in
                      (uu____27219, rest1))
             | uu____27230 -> ([], bindings1) in
           let uu____27237 = aux bindings in
           match uu____27237 with
           | (closing,bindings1) ->
               let uu____27262 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27262, bindings1) in
         match uu____27143 with
         | (q1,bindings1) ->
             let uu____27285 =
               let uu____27290 =
                 FStar_List.filter
                   (fun uu___147_27295  ->
                      match uu___147_27295 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27296 ->
                          false
                      | uu____27303 -> true) bindings1 in
               encode_env_bindings env uu____27290 in
             (match uu____27285 with
              | (env_decls,env1) ->
                  ((let uu____27321 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27321
                    then
                      let uu____27322 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27322
                    else ());
                   (let uu____27324 = encode_formula q1 env1 in
                    match uu____27324 with
                    | (phi,qdecls) ->
                        let uu____27345 =
                          let uu____27350 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27350 phi in
                        (match uu____27345 with
                         | (labels,phi1) ->
                             let uu____27367 = encode_labels labels in
                             (match uu____27367 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27404 =
                                      let uu____27411 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27412 =
                                        varops.mk_unique "@query" in
                                      (uu____27411,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27412) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27404 in
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
        let uu____27431 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27431 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27433 = encode_formula q env in
       match uu____27433 with
       | (f,uu____27439) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27441) -> true
             | uu____27446 -> false)))