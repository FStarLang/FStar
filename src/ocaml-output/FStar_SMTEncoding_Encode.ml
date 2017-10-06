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
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6186) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6196 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6196, [])
       | FStar_Syntax_Syntax.Tm_type uu____6199 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6203) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6228 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6228 with
            | (binders1,res) ->
                let uu____6239 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6239
                then
                  let uu____6244 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6244 with
                   | (vars,guards,env',decls,uu____6269) ->
                       let fsym =
                         let uu____6287 = varops.fresh "f" in
                         (uu____6287, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6290 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___157_6299 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___157_6299.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___157_6299.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___157_6299.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___157_6299.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___157_6299.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___157_6299.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___157_6299.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___157_6299.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___157_6299.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___157_6299.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___157_6299.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___157_6299.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___157_6299.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___157_6299.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___157_6299.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___157_6299.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___157_6299.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___157_6299.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___157_6299.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___157_6299.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___157_6299.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___157_6299.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___157_6299.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___157_6299.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___157_6299.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___157_6299.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___157_6299.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___157_6299.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___157_6299.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___157_6299.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___157_6299.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___157_6299.FStar_TypeChecker_Env.dsenv)
                            }) res in
                       (match uu____6290 with
                        | (pre_opt,res_t) ->
                            let uu____6310 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6310 with
                             | (res_pred,decls') ->
                                 let uu____6321 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6334 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6334, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6338 =
                                         encode_formula pre env' in
                                       (match uu____6338 with
                                        | (guard,decls0) ->
                                            let uu____6351 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6351, decls0)) in
                                 (match uu____6321 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6363 =
                                          let uu____6374 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6374) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6363 in
                                      let cvars =
                                        let uu____6392 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6392
                                          (FStar_List.filter
                                             (fun uu____6406  ->
                                                match uu____6406 with
                                                | (x,uu____6412) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6431 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6431 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6439 =
                                             let uu____6440 =
                                               let uu____6447 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6447) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6440 in
                                           (uu____6439,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6467 =
                                               let uu____6468 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6468 in
                                             varops.mk_unique uu____6467 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6479 =
                                               FStar_Options.log_queries () in
                                             if uu____6479
                                             then
                                               let uu____6482 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6482
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6490 =
                                               let uu____6497 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6497) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6490 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6509 =
                                               let uu____6516 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6516,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6509 in
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
                                             let uu____6537 =
                                               let uu____6544 =
                                                 let uu____6545 =
                                                   let uu____6556 =
                                                     let uu____6557 =
                                                       let uu____6562 =
                                                         let uu____6563 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6563 in
                                                       (f_has_t, uu____6562) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6557 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6556) in
                                                 mkForall_fuel uu____6545 in
                                               (uu____6544,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6537 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6586 =
                                               let uu____6593 =
                                                 let uu____6594 =
                                                   let uu____6605 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6605) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6594 in
                                               (uu____6593,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6586 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6630 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6630);
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
                     let uu____6645 =
                       let uu____6652 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6652,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6645 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6664 =
                       let uu____6671 =
                         let uu____6672 =
                           let uu____6683 =
                             let uu____6684 =
                               let uu____6689 =
                                 let uu____6690 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6690 in
                               (f_has_t, uu____6689) in
                             FStar_SMTEncoding_Util.mkImp uu____6684 in
                           ([[f_has_t]], [fsym], uu____6683) in
                         mkForall_fuel uu____6672 in
                       (uu____6671, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6664 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6717 ->
           let uu____6724 =
             let uu____6729 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6729 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6736;
                 FStar_Syntax_Syntax.vars = uu____6737;_} ->
                 let uu____6744 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6744 with
                  | (b,f1) ->
                      let uu____6769 =
                        let uu____6770 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6770 in
                      (uu____6769, f1))
             | uu____6779 -> failwith "impossible" in
           (match uu____6724 with
            | (x,f) ->
                let uu____6790 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6790 with
                 | (base_t,decls) ->
                     let uu____6801 = gen_term_var env x in
                     (match uu____6801 with
                      | (x1,xtm,env') ->
                          let uu____6815 = encode_formula f env' in
                          (match uu____6815 with
                           | (refinement,decls') ->
                               let uu____6826 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6826 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6842 =
                                        let uu____6845 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6852 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6845
                                          uu____6852 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6842 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6885  ->
                                              match uu____6885 with
                                              | (y,uu____6891) ->
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
                                    let uu____6924 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6924 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6932 =
                                           let uu____6933 =
                                             let uu____6940 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6940) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6933 in
                                         (uu____6932,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6961 =
                                             let uu____6962 =
                                               let uu____6963 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6963 in
                                             Prims.strcat module_name
                                               uu____6962 in
                                           varops.mk_unique uu____6961 in
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
                                           let uu____6977 =
                                             let uu____6984 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6984) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6977 in
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
                                           let uu____6999 =
                                             let uu____7006 =
                                               let uu____7007 =
                                                 let uu____7018 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7018) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7007 in
                                             (uu____7006,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6999 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____7044 =
                                             let uu____7051 =
                                               let uu____7052 =
                                                 let uu____7063 =
                                                   let uu____7064 =
                                                     let uu____7069 =
                                                       let uu____7070 =
                                                         let uu____7081 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____7081) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7070 in
                                                     (uu____7069, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7064 in
                                                 ([[valid_t]], cvars1,
                                                   uu____7063) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7052 in
                                             (uu____7051,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7044 in
                                         let t_kinding =
                                           let uu____7119 =
                                             let uu____7126 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____7126,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7119 in
                                         let t_interp =
                                           let uu____7144 =
                                             let uu____7151 =
                                               let uu____7152 =
                                                 let uu____7163 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7163) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7152 in
                                             let uu____7186 =
                                               let uu____7189 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7189 in
                                             (uu____7151, uu____7186,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7144 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7196 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7196);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7226 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7226 in
           let uu____7227 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7227 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7239 =
                    let uu____7246 =
                      let uu____7247 =
                        let uu____7248 =
                          let uu____7249 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7249 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7248 in
                      varops.mk_unique uu____7247 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7246) in
                  FStar_SMTEncoding_Util.mkAssume uu____7239 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7254 ->
           let uu____7269 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7269 with
            | (head1,args_e) ->
                let uu____7310 =
                  let uu____7323 =
                    let uu____7324 = FStar_Syntax_Subst.compress head1 in
                    uu____7324.FStar_Syntax_Syntax.n in
                  (uu____7323, args_e) in
                (match uu____7310 with
                 | uu____7339 when head_redex env head1 ->
                     let uu____7352 = whnf env t in
                     encode_term uu____7352 env
                 | uu____7353 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7372 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7386;
                       FStar_Syntax_Syntax.vars = uu____7387;_},uu____7388),uu____7389::
                    (v1,uu____7391)::(v2,uu____7393)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7444 = encode_term v1 env in
                     (match uu____7444 with
                      | (v11,decls1) ->
                          let uu____7455 = encode_term v2 env in
                          (match uu____7455 with
                           | (v21,decls2) ->
                               let uu____7466 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7466,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7470::(v1,uu____7472)::(v2,uu____7474)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7521 = encode_term v1 env in
                     (match uu____7521 with
                      | (v11,decls1) ->
                          let uu____7532 = encode_term v2 env in
                          (match uu____7532 with
                           | (v21,decls2) ->
                               let uu____7543 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7543,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7546) ->
                     let e0 =
                       let uu____7564 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7564 in
                     ((let uu____7572 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7572
                       then
                         let uu____7573 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7573
                       else ());
                      (let e =
                         let uu____7578 =
                           let uu____7579 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7580 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7579
                             uu____7580 in
                         uu____7578 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7589),(arg,uu____7591)::[]) -> encode_term arg env
                 | uu____7616 ->
                     let uu____7629 = encode_args args_e env in
                     (match uu____7629 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7684 = encode_term head1 env in
                            match uu____7684 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7748 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7748 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7826  ->
                                                 fun uu____7827  ->
                                                   match (uu____7826,
                                                           uu____7827)
                                                   with
                                                   | ((bv,uu____7849),
                                                      (a,uu____7851)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7869 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7869
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7874 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7874 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7889 =
                                                   let uu____7896 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7905 =
                                                     let uu____7906 =
                                                       let uu____7907 =
                                                         let uu____7908 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7908 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7907 in
                                                     varops.mk_unique
                                                       uu____7906 in
                                                   (uu____7896,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7905) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7889 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7925 = lookup_free_var_sym env fv in
                            match uu____7925 with
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
                                   FStar_Syntax_Syntax.pos = uu____7956;
                                   FStar_Syntax_Syntax.vars = uu____7957;_},uu____7958)
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
                                   FStar_Syntax_Syntax.pos = uu____7969;
                                   FStar_Syntax_Syntax.vars = uu____7970;_},uu____7971)
                                ->
                                let uu____7976 =
                                  let uu____7977 =
                                    let uu____7982 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7982
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7977
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7976
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8012 =
                                  let uu____8013 =
                                    let uu____8018 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____8018
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8013
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____8012
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8047,(FStar_Util.Inl t1,uu____8049),uu____8050)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8099,(FStar_Util.Inr c,uu____8101),uu____8102)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8151 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8178 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8178 in
                               let uu____8179 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8179 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8195;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8196;_},uu____8197)
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
                                     | uu____8211 ->
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
           let uu____8260 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8260 with
            | (bs1,body1,opening) ->
                let fallback uu____8283 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8290 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8290, [decl]) in
                let is_impure rc =
                  let uu____8297 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8297 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8307 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8307
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8327 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8327
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8331 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8331)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8338 =
                         let uu____8339 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8339 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8338);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8341 =
                       (is_impure rc) &&
                         (let uu____8343 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8343) in
                     if uu____8341
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8350 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8350 with
                        | (vars,guards,envbody,decls,uu____8375) ->
                            let body2 =
                              let uu____8389 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8389
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8391 = encode_term body2 envbody in
                            (match uu____8391 with
                             | (body3,decls') ->
                                 let uu____8402 =
                                   let uu____8411 = codomain_eff rc in
                                   match uu____8411 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8430 = encode_term tfun env in
                                       (match uu____8430 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8402 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8462 =
                                          let uu____8473 =
                                            let uu____8474 =
                                              let uu____8479 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8479, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8474 in
                                          ([], vars, uu____8473) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8462 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8491 =
                                              let uu____8494 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8494
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8491 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8513 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8513 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8521 =
                                             let uu____8522 =
                                               let uu____8529 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8529) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8522 in
                                           (uu____8521,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8540 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8540 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8551 =
                                                    let uu____8552 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8552 = cache_size in
                                                  if uu____8551
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
                                                    let uu____8568 =
                                                      let uu____8569 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8569 in
                                                    varops.mk_unique
                                                      uu____8568 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8576 =
                                                    let uu____8583 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8583) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8576 in
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
                                                      let uu____8601 =
                                                        let uu____8602 =
                                                          let uu____8609 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8609,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8602 in
                                                      [uu____8601] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8622 =
                                                    let uu____8629 =
                                                      let uu____8630 =
                                                        let uu____8641 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8641) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8630 in
                                                    (uu____8629,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8622 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8658 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8658);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8661,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8662;
                          FStar_Syntax_Syntax.lbunivs = uu____8663;
                          FStar_Syntax_Syntax.lbtyp = uu____8664;
                          FStar_Syntax_Syntax.lbeff = uu____8665;
                          FStar_Syntax_Syntax.lbdef = uu____8666;_}::uu____8667),uu____8668)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8694;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8696;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8717 ->
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
              let uu____8787 = encode_term e1 env in
              match uu____8787 with
              | (ee1,decls1) ->
                  let uu____8798 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8798 with
                   | (xs,e21) ->
                       let uu____8823 = FStar_List.hd xs in
                       (match uu____8823 with
                        | (x1,uu____8837) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8839 = encode_body e21 env' in
                            (match uu____8839 with
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
            let uu____8871 =
              let uu____8878 =
                let uu____8879 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8879 in
              gen_term_var env uu____8878 in
            match uu____8871 with
            | (scrsym,scr',env1) ->
                let uu____8887 = encode_term e env1 in
                (match uu____8887 with
                 | (scr,decls) ->
                     let uu____8898 =
                       let encode_branch b uu____8923 =
                         match uu____8923 with
                         | (else_case,decls1) ->
                             let uu____8942 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8942 with
                              | (p,w,br) ->
                                  let uu____8968 = encode_pat env1 p in
                                  (match uu____8968 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9005  ->
                                                   match uu____9005 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9012 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9034 =
                                               encode_term w1 env2 in
                                             (match uu____9034 with
                                              | (w2,decls2) ->
                                                  let uu____9047 =
                                                    let uu____9048 =
                                                      let uu____9053 =
                                                        let uu____9054 =
                                                          let uu____9059 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9059) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9054 in
                                                      (guard, uu____9053) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9048 in
                                                  (uu____9047, decls2)) in
                                       (match uu____9012 with
                                        | (guard1,decls2) ->
                                            let uu____9072 =
                                              encode_br br env2 in
                                            (match uu____9072 with
                                             | (br1,decls3) ->
                                                 let uu____9085 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9085,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8898 with
                      | (match_tm,decls1) ->
                          let uu____9104 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9104, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9144 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9144
       then
         let uu____9145 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9145
       else ());
      (let uu____9147 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9147 with
       | (vars,pat_term) ->
           let uu____9164 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9217  ->
                     fun v1  ->
                       match uu____9217 with
                       | (env1,vars1) ->
                           let uu____9269 = gen_term_var env1 v1 in
                           (match uu____9269 with
                            | (xx,uu____9291,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9164 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9370 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9371 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9372 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9380 = encode_const c env1 in
                      (match uu____9380 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9394::uu____9395 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9398 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9421 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9421 with
                        | (uu____9428,uu____9429::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9432 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9465  ->
                                  match uu____9465 with
                                  | (arg,uu____9473) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9479 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9479)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9506) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9537 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9560 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9604  ->
                                  match uu____9604 with
                                  | (arg,uu____9618) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9624 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9624)) in
                      FStar_All.pipe_right uu____9560 FStar_List.flatten in
                let pat_term1 uu____9652 = encode_term pat_term env1 in
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
      let uu____9662 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9700  ->
                fun uu____9701  ->
                  match (uu____9700, uu____9701) with
                  | ((tms,decls),(t,uu____9737)) ->
                      let uu____9758 = encode_term t env in
                      (match uu____9758 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9662 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9815 = FStar_Syntax_Util.list_elements e in
        match uu____9815 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9836 =
          let uu____9851 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9851 FStar_Syntax_Util.head_and_args in
        match uu____9836 with
        | (head1,args) ->
            let uu____9890 =
              let uu____9903 =
                let uu____9904 = FStar_Syntax_Util.un_uinst head1 in
                uu____9904.FStar_Syntax_Syntax.n in
              (uu____9903, args) in
            (match uu____9890 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9918,uu____9919)::(e,uu____9921)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9956 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9992 =
            let uu____10007 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10007 FStar_Syntax_Util.head_and_args in
          match uu____9992 with
          | (head1,args) ->
              let uu____10048 =
                let uu____10061 =
                  let uu____10062 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10062.FStar_Syntax_Syntax.n in
                (uu____10061, args) in
              (match uu____10048 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10079)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10106 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10128 = smt_pat_or1 t1 in
            (match uu____10128 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10144 = list_elements1 e in
                 FStar_All.pipe_right uu____10144
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10162 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10162
                           (FStar_List.map one_pat)))
             | uu____10173 ->
                 let uu____10178 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10178])
        | uu____10199 ->
            let uu____10202 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10202] in
      let uu____10223 =
        let uu____10242 =
          let uu____10243 = FStar_Syntax_Subst.compress t in
          uu____10243.FStar_Syntax_Syntax.n in
        match uu____10242 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10282 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10282 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10325;
                        FStar_Syntax_Syntax.effect_name = uu____10326;
                        FStar_Syntax_Syntax.result_typ = uu____10327;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10329)::(post,uu____10331)::(pats,uu____10333)::[];
                        FStar_Syntax_Syntax.flags = uu____10334;_}
                      ->
                      let uu____10375 = lemma_pats pats in
                      (binders1, pre, post, uu____10375)
                  | uu____10392 -> failwith "impos"))
        | uu____10411 -> failwith "Impos" in
      match uu____10223 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___158_10459 = env in
            {
              bindings = (uu___158_10459.bindings);
              depth = (uu___158_10459.depth);
              tcenv = (uu___158_10459.tcenv);
              warn = (uu___158_10459.warn);
              cache = (uu___158_10459.cache);
              nolabels = (uu___158_10459.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___158_10459.encode_non_total_function_typ);
              current_module_name = (uu___158_10459.current_module_name)
            } in
          let uu____10460 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10460 with
           | (vars,guards,env2,decls,uu____10485) ->
               let uu____10498 =
                 let uu____10511 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10555 =
                             let uu____10564 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10564
                               FStar_List.unzip in
                           match uu____10555 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10511 FStar_List.unzip in
               (match uu____10498 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___159_10673 = env2 in
                      {
                        bindings = (uu___159_10673.bindings);
                        depth = (uu___159_10673.depth);
                        tcenv = (uu___159_10673.tcenv);
                        warn = (uu___159_10673.warn);
                        cache = (uu___159_10673.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___159_10673.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___159_10673.encode_non_total_function_typ);
                        current_module_name =
                          (uu___159_10673.current_module_name)
                      } in
                    let uu____10674 =
                      let uu____10679 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10679 env3 in
                    (match uu____10674 with
                     | (pre1,decls'') ->
                         let uu____10686 =
                           let uu____10691 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10691 env3 in
                         (match uu____10686 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10701 =
                                let uu____10702 =
                                  let uu____10713 =
                                    let uu____10714 =
                                      let uu____10719 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10719, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10714 in
                                  (pats, vars, uu____10713) in
                                FStar_SMTEncoding_Util.mkForall uu____10702 in
                              (uu____10701, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10738 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10738
        then
          let uu____10739 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10740 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10739 uu____10740
        else () in
      let enc f r l =
        let uu____10773 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10801 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10801 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10773 with
        | (decls,args) ->
            let uu____10830 =
              let uu___160_10831 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___160_10831.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___160_10831.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10830, decls) in
      let const_op f r uu____10862 =
        let uu____10875 = f r in (uu____10875, []) in
      let un_op f l =
        let uu____10894 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10894 in
      let bin_op f uu___134_10910 =
        match uu___134_10910 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10921 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10955 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10978  ->
                 match uu____10978 with
                 | (t,uu____10992) ->
                     let uu____10993 = encode_formula t env in
                     (match uu____10993 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10955 with
        | (decls,phis) ->
            let uu____11022 =
              let uu___161_11023 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___161_11023.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___161_11023.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11022, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11084  ->
               match uu____11084 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11103) -> false
                    | uu____11104 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11119 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11119
        else
          (let uu____11133 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11133 r rf) in
      let mk_imp1 r uu___135_11158 =
        match uu___135_11158 with
        | (lhs,uu____11164)::(rhs,uu____11166)::[] ->
            let uu____11193 = encode_formula rhs env in
            (match uu____11193 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11208) ->
                      (l1, decls1)
                  | uu____11213 ->
                      let uu____11214 = encode_formula lhs env in
                      (match uu____11214 with
                       | (l2,decls2) ->
                           let uu____11225 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11225, (FStar_List.append decls1 decls2)))))
        | uu____11228 -> failwith "impossible" in
      let mk_ite r uu___136_11249 =
        match uu___136_11249 with
        | (guard,uu____11255)::(_then,uu____11257)::(_else,uu____11259)::[]
            ->
            let uu____11296 = encode_formula guard env in
            (match uu____11296 with
             | (g,decls1) ->
                 let uu____11307 = encode_formula _then env in
                 (match uu____11307 with
                  | (t,decls2) ->
                      let uu____11318 = encode_formula _else env in
                      (match uu____11318 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11332 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11357 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11357 in
      let connectives =
        let uu____11375 =
          let uu____11388 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11388) in
        let uu____11405 =
          let uu____11420 =
            let uu____11433 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11433) in
          let uu____11450 =
            let uu____11465 =
              let uu____11480 =
                let uu____11493 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11493) in
              let uu____11510 =
                let uu____11525 =
                  let uu____11540 =
                    let uu____11553 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11553) in
                  [uu____11540;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11525 in
              uu____11480 :: uu____11510 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11465 in
          uu____11420 :: uu____11450 in
        uu____11375 :: uu____11405 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11874 = encode_formula phi' env in
            (match uu____11874 with
             | (phi2,decls) ->
                 let uu____11885 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11885, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11886 ->
            let uu____11893 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11893 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11932 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11932 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11944;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11946;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11967 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11967 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12014::(x,uu____12016)::(t,uu____12018)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12065 = encode_term x env in
                 (match uu____12065 with
                  | (x1,decls) ->
                      let uu____12076 = encode_term t env in
                      (match uu____12076 with
                       | (t1,decls') ->
                           let uu____12087 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12087, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12092)::(msg,uu____12094)::(phi2,uu____12096)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12141 =
                   let uu____12146 =
                     let uu____12147 = FStar_Syntax_Subst.compress r in
                     uu____12147.FStar_Syntax_Syntax.n in
                   let uu____12150 =
                     let uu____12151 = FStar_Syntax_Subst.compress msg in
                     uu____12151.FStar_Syntax_Syntax.n in
                   (uu____12146, uu____12150) in
                 (match uu____12141 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12160))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12166 -> fallback phi2)
             | uu____12171 when head_redex env head2 ->
                 let uu____12184 = whnf env phi1 in
                 encode_formula uu____12184 env
             | uu____12185 ->
                 let uu____12198 = encode_term phi1 env in
                 (match uu____12198 with
                  | (tt,decls) ->
                      let uu____12209 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___162_12212 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___162_12212.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___162_12212.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12209, decls)))
        | uu____12213 ->
            let uu____12214 = encode_term phi1 env in
            (match uu____12214 with
             | (tt,decls) ->
                 let uu____12225 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___163_12228 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___163_12228.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___163_12228.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12225, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12264 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12264 with
        | (vars,guards,env2,decls,uu____12303) ->
            let uu____12316 =
              let uu____12329 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12377 =
                          let uu____12386 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12416  ->
                                    match uu____12416 with
                                    | (t,uu____12426) ->
                                        encode_term t
                                          (let uu___164_12428 = env2 in
                                           {
                                             bindings =
                                               (uu___164_12428.bindings);
                                             depth = (uu___164_12428.depth);
                                             tcenv = (uu___164_12428.tcenv);
                                             warn = (uu___164_12428.warn);
                                             cache = (uu___164_12428.cache);
                                             nolabels =
                                               (uu___164_12428.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___164_12428.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___164_12428.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12386 FStar_List.unzip in
                        match uu____12377 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12329 FStar_List.unzip in
            (match uu____12316 with
             | (pats,decls') ->
                 let uu____12527 = encode_formula body env2 in
                 (match uu____12527 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12559;
                             FStar_SMTEncoding_Term.rng = uu____12560;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12575 -> guards in
                      let uu____12580 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12580, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12640  ->
                   match uu____12640 with
                   | (x,uu____12646) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12654 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12666 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12666) uu____12654 tl1 in
             let uu____12669 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12696  ->
                       match uu____12696 with
                       | (b,uu____12702) ->
                           let uu____12703 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12703)) in
             (match uu____12669 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12709) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12723 =
                    let uu____12724 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12724 in
                  FStar_Errors.warn pos uu____12723) in
       let uu____12725 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12725 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12734 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12792  ->
                     match uu____12792 with
                     | (l,uu____12806) -> FStar_Ident.lid_equals op l)) in
           (match uu____12734 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12839,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12879 = encode_q_body env vars pats body in
             match uu____12879 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12924 =
                     let uu____12935 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12935) in
                   FStar_SMTEncoding_Term.mkForall uu____12924
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12954 = encode_q_body env vars pats body in
             match uu____12954 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12998 =
                   let uu____12999 =
                     let uu____13010 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13010) in
                   FStar_SMTEncoding_Term.mkExists uu____12999
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12998, decls))))
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
  let uu____13108 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13108 with
  | (asym,a) ->
      let uu____13115 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13115 with
       | (xsym,x) ->
           let uu____13122 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13122 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13166 =
                      let uu____13177 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13177, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13166 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13203 =
                      let uu____13210 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13210) in
                    FStar_SMTEncoding_Util.mkApp uu____13203 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13223 =
                    let uu____13226 =
                      let uu____13229 =
                        let uu____13232 =
                          let uu____13233 =
                            let uu____13240 =
                              let uu____13241 =
                                let uu____13252 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13252) in
                              FStar_SMTEncoding_Util.mkForall uu____13241 in
                            (uu____13240, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13233 in
                        let uu____13269 =
                          let uu____13272 =
                            let uu____13273 =
                              let uu____13280 =
                                let uu____13281 =
                                  let uu____13292 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13292) in
                                FStar_SMTEncoding_Util.mkForall uu____13281 in
                              (uu____13280,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13273 in
                          [uu____13272] in
                        uu____13232 :: uu____13269 in
                      xtok_decl :: uu____13229 in
                    xname_decl :: uu____13226 in
                  (xtok1, uu____13223) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13383 =
                    let uu____13396 =
                      let uu____13405 =
                        let uu____13406 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13406 in
                      quant axy uu____13405 in
                    (FStar_Parser_Const.op_Eq, uu____13396) in
                  let uu____13415 =
                    let uu____13430 =
                      let uu____13443 =
                        let uu____13452 =
                          let uu____13453 =
                            let uu____13454 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13454 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13453 in
                        quant axy uu____13452 in
                      (FStar_Parser_Const.op_notEq, uu____13443) in
                    let uu____13463 =
                      let uu____13478 =
                        let uu____13491 =
                          let uu____13500 =
                            let uu____13501 =
                              let uu____13502 =
                                let uu____13507 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13508 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13507, uu____13508) in
                              FStar_SMTEncoding_Util.mkLT uu____13502 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13501 in
                          quant xy uu____13500 in
                        (FStar_Parser_Const.op_LT, uu____13491) in
                      let uu____13517 =
                        let uu____13532 =
                          let uu____13545 =
                            let uu____13554 =
                              let uu____13555 =
                                let uu____13556 =
                                  let uu____13561 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13562 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13561, uu____13562) in
                                FStar_SMTEncoding_Util.mkLTE uu____13556 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13555 in
                            quant xy uu____13554 in
                          (FStar_Parser_Const.op_LTE, uu____13545) in
                        let uu____13571 =
                          let uu____13586 =
                            let uu____13599 =
                              let uu____13608 =
                                let uu____13609 =
                                  let uu____13610 =
                                    let uu____13615 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13616 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13615, uu____13616) in
                                  FStar_SMTEncoding_Util.mkGT uu____13610 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13609 in
                              quant xy uu____13608 in
                            (FStar_Parser_Const.op_GT, uu____13599) in
                          let uu____13625 =
                            let uu____13640 =
                              let uu____13653 =
                                let uu____13662 =
                                  let uu____13663 =
                                    let uu____13664 =
                                      let uu____13669 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13670 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13669, uu____13670) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13664 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13663 in
                                quant xy uu____13662 in
                              (FStar_Parser_Const.op_GTE, uu____13653) in
                            let uu____13679 =
                              let uu____13694 =
                                let uu____13707 =
                                  let uu____13716 =
                                    let uu____13717 =
                                      let uu____13718 =
                                        let uu____13723 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13724 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13723, uu____13724) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13718 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13717 in
                                  quant xy uu____13716 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13707) in
                              let uu____13733 =
                                let uu____13748 =
                                  let uu____13761 =
                                    let uu____13770 =
                                      let uu____13771 =
                                        let uu____13772 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13772 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13771 in
                                    quant qx uu____13770 in
                                  (FStar_Parser_Const.op_Minus, uu____13761) in
                                let uu____13781 =
                                  let uu____13796 =
                                    let uu____13809 =
                                      let uu____13818 =
                                        let uu____13819 =
                                          let uu____13820 =
                                            let uu____13825 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13826 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13825, uu____13826) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13820 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13819 in
                                      quant xy uu____13818 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13809) in
                                  let uu____13835 =
                                    let uu____13850 =
                                      let uu____13863 =
                                        let uu____13872 =
                                          let uu____13873 =
                                            let uu____13874 =
                                              let uu____13879 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13880 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13879, uu____13880) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13874 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13873 in
                                        quant xy uu____13872 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13863) in
                                    let uu____13889 =
                                      let uu____13904 =
                                        let uu____13917 =
                                          let uu____13926 =
                                            let uu____13927 =
                                              let uu____13928 =
                                                let uu____13933 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13934 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13933, uu____13934) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13928 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13927 in
                                          quant xy uu____13926 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13917) in
                                      let uu____13943 =
                                        let uu____13958 =
                                          let uu____13971 =
                                            let uu____13980 =
                                              let uu____13981 =
                                                let uu____13982 =
                                                  let uu____13987 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13988 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13987, uu____13988) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13982 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13981 in
                                            quant xy uu____13980 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13971) in
                                        let uu____13997 =
                                          let uu____14012 =
                                            let uu____14025 =
                                              let uu____14034 =
                                                let uu____14035 =
                                                  let uu____14036 =
                                                    let uu____14041 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14042 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14041,
                                                      uu____14042) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14036 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14035 in
                                              quant xy uu____14034 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14025) in
                                          let uu____14051 =
                                            let uu____14066 =
                                              let uu____14079 =
                                                let uu____14088 =
                                                  let uu____14089 =
                                                    let uu____14090 =
                                                      let uu____14095 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14096 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14095,
                                                        uu____14096) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14090 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14089 in
                                                quant xy uu____14088 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14079) in
                                            let uu____14105 =
                                              let uu____14120 =
                                                let uu____14133 =
                                                  let uu____14142 =
                                                    let uu____14143 =
                                                      let uu____14144 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14144 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14143 in
                                                  quant qx uu____14142 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14133) in
                                              [uu____14120] in
                                            uu____14066 :: uu____14105 in
                                          uu____14012 :: uu____14051 in
                                        uu____13958 :: uu____13997 in
                                      uu____13904 :: uu____13943 in
                                    uu____13850 :: uu____13889 in
                                  uu____13796 :: uu____13835 in
                                uu____13748 :: uu____13781 in
                              uu____13694 :: uu____13733 in
                            uu____13640 :: uu____13679 in
                          uu____13586 :: uu____13625 in
                        uu____13532 :: uu____13571 in
                      uu____13478 :: uu____13517 in
                    uu____13430 :: uu____13463 in
                  uu____13383 :: uu____13415 in
                let mk1 l v1 =
                  let uu____14358 =
                    let uu____14367 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14425  ->
                              match uu____14425 with
                              | (l',uu____14439) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14367
                      (FStar_Option.map
                         (fun uu____14499  ->
                            match uu____14499 with | (uu____14518,b) -> b v1)) in
                  FStar_All.pipe_right uu____14358 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14589  ->
                          match uu____14589 with
                          | (l',uu____14603) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14644 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14644 with
        | (xxsym,xx) ->
            let uu____14651 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14651 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14661 =
                   let uu____14668 =
                     let uu____14669 =
                       let uu____14680 =
                         let uu____14681 =
                           let uu____14686 =
                             let uu____14687 =
                               let uu____14692 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14692) in
                             FStar_SMTEncoding_Util.mkEq uu____14687 in
                           (xx_has_type, uu____14686) in
                         FStar_SMTEncoding_Util.mkImp uu____14681 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14680) in
                     FStar_SMTEncoding_Util.mkForall uu____14669 in
                   let uu____14717 =
                     let uu____14718 =
                       let uu____14719 =
                         let uu____14720 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14720 in
                       Prims.strcat module_name uu____14719 in
                     varops.mk_unique uu____14718 in
                   (uu____14668, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14717) in
                 FStar_SMTEncoding_Util.mkAssume uu____14661)
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
    let uu____14760 =
      let uu____14761 =
        let uu____14768 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14768, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14761 in
    let uu____14771 =
      let uu____14774 =
        let uu____14775 =
          let uu____14782 =
            let uu____14783 =
              let uu____14794 =
                let uu____14795 =
                  let uu____14800 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14800) in
                FStar_SMTEncoding_Util.mkImp uu____14795 in
              ([[typing_pred]], [xx], uu____14794) in
            mkForall_fuel uu____14783 in
          (uu____14782, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14775 in
      [uu____14774] in
    uu____14760 :: uu____14771 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14842 =
      let uu____14843 =
        let uu____14850 =
          let uu____14851 =
            let uu____14862 =
              let uu____14867 =
                let uu____14870 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14870] in
              [uu____14867] in
            let uu____14875 =
              let uu____14876 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14876 tt in
            (uu____14862, [bb], uu____14875) in
          FStar_SMTEncoding_Util.mkForall uu____14851 in
        (uu____14850, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14843 in
    let uu____14897 =
      let uu____14900 =
        let uu____14901 =
          let uu____14908 =
            let uu____14909 =
              let uu____14920 =
                let uu____14921 =
                  let uu____14926 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14926) in
                FStar_SMTEncoding_Util.mkImp uu____14921 in
              ([[typing_pred]], [xx], uu____14920) in
            mkForall_fuel uu____14909 in
          (uu____14908, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14901 in
      [uu____14900] in
    uu____14842 :: uu____14897 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14976 =
        let uu____14977 =
          let uu____14984 =
            let uu____14987 =
              let uu____14990 =
                let uu____14993 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14994 =
                  let uu____14997 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14997] in
                uu____14993 :: uu____14994 in
              tt :: uu____14990 in
            tt :: uu____14987 in
          ("Prims.Precedes", uu____14984) in
        FStar_SMTEncoding_Util.mkApp uu____14977 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14976 in
    let precedes_y_x =
      let uu____15001 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15001 in
    let uu____15004 =
      let uu____15005 =
        let uu____15012 =
          let uu____15013 =
            let uu____15024 =
              let uu____15029 =
                let uu____15032 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15032] in
              [uu____15029] in
            let uu____15037 =
              let uu____15038 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15038 tt in
            (uu____15024, [bb], uu____15037) in
          FStar_SMTEncoding_Util.mkForall uu____15013 in
        (uu____15012, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15005 in
    let uu____15059 =
      let uu____15062 =
        let uu____15063 =
          let uu____15070 =
            let uu____15071 =
              let uu____15082 =
                let uu____15083 =
                  let uu____15088 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15088) in
                FStar_SMTEncoding_Util.mkImp uu____15083 in
              ([[typing_pred]], [xx], uu____15082) in
            mkForall_fuel uu____15071 in
          (uu____15070, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15063 in
      let uu____15113 =
        let uu____15116 =
          let uu____15117 =
            let uu____15124 =
              let uu____15125 =
                let uu____15136 =
                  let uu____15137 =
                    let uu____15142 =
                      let uu____15143 =
                        let uu____15146 =
                          let uu____15149 =
                            let uu____15152 =
                              let uu____15153 =
                                let uu____15158 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15159 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15158, uu____15159) in
                              FStar_SMTEncoding_Util.mkGT uu____15153 in
                            let uu____15160 =
                              let uu____15163 =
                                let uu____15164 =
                                  let uu____15169 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15170 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15169, uu____15170) in
                                FStar_SMTEncoding_Util.mkGTE uu____15164 in
                              let uu____15171 =
                                let uu____15174 =
                                  let uu____15175 =
                                    let uu____15180 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15181 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15180, uu____15181) in
                                  FStar_SMTEncoding_Util.mkLT uu____15175 in
                                [uu____15174] in
                              uu____15163 :: uu____15171 in
                            uu____15152 :: uu____15160 in
                          typing_pred_y :: uu____15149 in
                        typing_pred :: uu____15146 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15143 in
                    (uu____15142, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15137 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15136) in
              mkForall_fuel uu____15125 in
            (uu____15124,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15117 in
        [uu____15116] in
      uu____15062 :: uu____15113 in
    uu____15004 :: uu____15059 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15227 =
      let uu____15228 =
        let uu____15235 =
          let uu____15236 =
            let uu____15247 =
              let uu____15252 =
                let uu____15255 = FStar_SMTEncoding_Term.boxString b in
                [uu____15255] in
              [uu____15252] in
            let uu____15260 =
              let uu____15261 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15261 tt in
            (uu____15247, [bb], uu____15260) in
          FStar_SMTEncoding_Util.mkForall uu____15236 in
        (uu____15235, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15228 in
    let uu____15282 =
      let uu____15285 =
        let uu____15286 =
          let uu____15293 =
            let uu____15294 =
              let uu____15305 =
                let uu____15306 =
                  let uu____15311 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15311) in
                FStar_SMTEncoding_Util.mkImp uu____15306 in
              ([[typing_pred]], [xx], uu____15305) in
            mkForall_fuel uu____15294 in
          (uu____15293, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15286 in
      [uu____15285] in
    uu____15227 :: uu____15282 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15364 =
      let uu____15365 =
        let uu____15372 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15372, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15365 in
    [uu____15364] in
  let mk_and_interp env conj uu____15384 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15409 =
      let uu____15410 =
        let uu____15417 =
          let uu____15418 =
            let uu____15429 =
              let uu____15430 =
                let uu____15435 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15435, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15430 in
            ([[l_and_a_b]], [aa; bb], uu____15429) in
          FStar_SMTEncoding_Util.mkForall uu____15418 in
        (uu____15417, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15410 in
    [uu____15409] in
  let mk_or_interp env disj uu____15473 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15498 =
      let uu____15499 =
        let uu____15506 =
          let uu____15507 =
            let uu____15518 =
              let uu____15519 =
                let uu____15524 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15524, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15519 in
            ([[l_or_a_b]], [aa; bb], uu____15518) in
          FStar_SMTEncoding_Util.mkForall uu____15507 in
        (uu____15506, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15499 in
    [uu____15498] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15587 =
      let uu____15588 =
        let uu____15595 =
          let uu____15596 =
            let uu____15607 =
              let uu____15608 =
                let uu____15613 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15613, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15608 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15607) in
          FStar_SMTEncoding_Util.mkForall uu____15596 in
        (uu____15595, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15588 in
    [uu____15587] in
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
    let uu____15686 =
      let uu____15687 =
        let uu____15694 =
          let uu____15695 =
            let uu____15706 =
              let uu____15707 =
                let uu____15712 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15712, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15707 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15706) in
          FStar_SMTEncoding_Util.mkForall uu____15695 in
        (uu____15694, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15687 in
    [uu____15686] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15783 =
      let uu____15784 =
        let uu____15791 =
          let uu____15792 =
            let uu____15803 =
              let uu____15804 =
                let uu____15809 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15809, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15804 in
            ([[l_imp_a_b]], [aa; bb], uu____15803) in
          FStar_SMTEncoding_Util.mkForall uu____15792 in
        (uu____15791, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15784 in
    [uu____15783] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15872 =
      let uu____15873 =
        let uu____15880 =
          let uu____15881 =
            let uu____15892 =
              let uu____15893 =
                let uu____15898 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15898, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15893 in
            ([[l_iff_a_b]], [aa; bb], uu____15892) in
          FStar_SMTEncoding_Util.mkForall uu____15881 in
        (uu____15880, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15873 in
    [uu____15872] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15950 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15950 in
    let uu____15953 =
      let uu____15954 =
        let uu____15961 =
          let uu____15962 =
            let uu____15973 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15973) in
          FStar_SMTEncoding_Util.mkForall uu____15962 in
        (uu____15961, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15954 in
    [uu____15953] in
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
      let uu____16033 =
        let uu____16040 =
          let uu____16043 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16043] in
        ("Valid", uu____16040) in
      FStar_SMTEncoding_Util.mkApp uu____16033 in
    let uu____16046 =
      let uu____16047 =
        let uu____16054 =
          let uu____16055 =
            let uu____16066 =
              let uu____16067 =
                let uu____16072 =
                  let uu____16073 =
                    let uu____16084 =
                      let uu____16089 =
                        let uu____16092 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16092] in
                      [uu____16089] in
                    let uu____16097 =
                      let uu____16098 =
                        let uu____16103 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16103, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16098 in
                    (uu____16084, [xx1], uu____16097) in
                  FStar_SMTEncoding_Util.mkForall uu____16073 in
                (uu____16072, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16067 in
            ([[l_forall_a_b]], [aa; bb], uu____16066) in
          FStar_SMTEncoding_Util.mkForall uu____16055 in
        (uu____16054, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16047 in
    [uu____16046] in
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
      let uu____16185 =
        let uu____16192 =
          let uu____16195 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16195] in
        ("Valid", uu____16192) in
      FStar_SMTEncoding_Util.mkApp uu____16185 in
    let uu____16198 =
      let uu____16199 =
        let uu____16206 =
          let uu____16207 =
            let uu____16218 =
              let uu____16219 =
                let uu____16224 =
                  let uu____16225 =
                    let uu____16236 =
                      let uu____16241 =
                        let uu____16244 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16244] in
                      [uu____16241] in
                    let uu____16249 =
                      let uu____16250 =
                        let uu____16255 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16255, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16250 in
                    (uu____16236, [xx1], uu____16249) in
                  FStar_SMTEncoding_Util.mkExists uu____16225 in
                (uu____16224, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16219 in
            ([[l_exists_a_b]], [aa; bb], uu____16218) in
          FStar_SMTEncoding_Util.mkForall uu____16207 in
        (uu____16206, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16199 in
    [uu____16198] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16315 =
      let uu____16316 =
        let uu____16323 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16324 = varops.mk_unique "typing_range_const" in
        (uu____16323, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16324) in
      FStar_SMTEncoding_Util.mkAssume uu____16316 in
    [uu____16315] in
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
        let uu____16358 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16358 x1 t in
      let uu____16359 =
        let uu____16370 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16370) in
      FStar_SMTEncoding_Util.mkForall uu____16359 in
    let uu____16393 =
      let uu____16394 =
        let uu____16401 =
          let uu____16402 =
            let uu____16413 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16413) in
          FStar_SMTEncoding_Util.mkForall uu____16402 in
        (uu____16401,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16394 in
    [uu____16393] in
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
          let uu____16737 =
            FStar_Util.find_opt
              (fun uu____16763  ->
                 match uu____16763 with
                 | (l,uu____16775) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16737 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16800,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16839 = encode_function_type_as_formula t env in
        match uu____16839 with
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
              let uu____16885 =
                ((let uu____16888 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16888) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16885
              then
                let uu____16895 = new_term_constant_and_tok_from_lid env lid in
                match uu____16895 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16914 =
                        let uu____16915 = FStar_Syntax_Subst.compress t_norm in
                        uu____16915.FStar_Syntax_Syntax.n in
                      match uu____16914 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16921) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16951  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16956 -> [] in
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
                (let uu____16970 = prims.is lid in
                 if uu____16970
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16978 = prims.mk lid vname in
                   match uu____16978 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____17002 =
                      let uu____17013 = curried_arrow_formals_comp t_norm in
                      match uu____17013 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17031 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____17031
                            then
                              let uu____17032 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___165_17035 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___165_17035.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___165_17035.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___165_17035.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___165_17035.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___165_17035.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___165_17035.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___165_17035.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___165_17035.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___165_17035.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___165_17035.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___165_17035.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___165_17035.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___165_17035.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___165_17035.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___165_17035.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___165_17035.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___165_17035.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___165_17035.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___165_17035.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___165_17035.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___165_17035.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___165_17035.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___165_17035.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___165_17035.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___165_17035.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___165_17035.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___165_17035.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___165_17035.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___165_17035.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___165_17035.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___165_17035.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___165_17035.FStar_TypeChecker_Env.dsenv)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____17032
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____17047 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____17047)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____17002 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17092 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____17092 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17113 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___137_17155  ->
                                       match uu___137_17155 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17159 =
                                             FStar_Util.prefix vars in
                                           (match uu____17159 with
                                            | (uu____17180,(xxsym,uu____17182))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17200 =
                                                  let uu____17201 =
                                                    let uu____17208 =
                                                      let uu____17209 =
                                                        let uu____17220 =
                                                          let uu____17221 =
                                                            let uu____17226 =
                                                              let uu____17227
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17227 in
                                                            (vapp,
                                                              uu____17226) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17221 in
                                                        ([[vapp]], vars,
                                                          uu____17220) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17209 in
                                                    (uu____17208,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17201 in
                                                [uu____17200])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17246 =
                                             FStar_Util.prefix vars in
                                           (match uu____17246 with
                                            | (uu____17267,(xxsym,uu____17269))
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
                                                let uu____17292 =
                                                  let uu____17293 =
                                                    let uu____17300 =
                                                      let uu____17301 =
                                                        let uu____17312 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17312) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17301 in
                                                    (uu____17300,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17293 in
                                                [uu____17292])
                                       | uu____17329 -> [])) in
                             let uu____17330 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17330 with
                              | (vars,guards,env',decls1,uu____17357) ->
                                  let uu____17370 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17379 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17379, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17381 =
                                          encode_formula p env' in
                                        (match uu____17381 with
                                         | (g,ds) ->
                                             let uu____17392 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17392,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17370 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17405 =
                                           let uu____17412 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17412) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17405 in
                                       let uu____17421 =
                                         let vname_decl =
                                           let uu____17429 =
                                             let uu____17440 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17450  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17440,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17429 in
                                         let uu____17459 =
                                           let env2 =
                                             let uu___166_17465 = env1 in
                                             {
                                               bindings =
                                                 (uu___166_17465.bindings);
                                               depth = (uu___166_17465.depth);
                                               tcenv = (uu___166_17465.tcenv);
                                               warn = (uu___166_17465.warn);
                                               cache = (uu___166_17465.cache);
                                               nolabels =
                                                 (uu___166_17465.nolabels);
                                               use_zfuel_name =
                                                 (uu___166_17465.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___166_17465.current_module_name)
                                             } in
                                           let uu____17466 =
                                             let uu____17467 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17467 in
                                           if uu____17466
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17459 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17482::uu____17483 ->
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
                                                     let uu____17523 =
                                                       let uu____17534 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17534) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17523 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17561 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17564 =
                                               match formals with
                                               | [] ->
                                                   let uu____17581 =
                                                     let uu____17582 =
                                                       let uu____17585 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17585 in
                                                     push_free_var env1 lid
                                                       vname uu____17582 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17581)
                                               | uu____17590 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17597 =
                                                       let uu____17604 =
                                                         let uu____17605 =
                                                           let uu____17616 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17616) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17605 in
                                                       (uu____17604,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17597 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17564 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17421 with
                                        | (decls2,env2) ->
                                            let uu____17659 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17667 =
                                                encode_term res_t1 env' in
                                              match uu____17667 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17680 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17680, decls) in
                                            (match uu____17659 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17691 =
                                                     let uu____17698 =
                                                       let uu____17699 =
                                                         let uu____17710 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17710) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17699 in
                                                     (uu____17698,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17691 in
                                                 let freshness =
                                                   let uu____17726 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17726
                                                   then
                                                     let uu____17731 =
                                                       let uu____17732 =
                                                         let uu____17743 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17754 =
                                                           varops.next_id () in
                                                         (vname, uu____17743,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17754) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17732 in
                                                     let uu____17757 =
                                                       let uu____17760 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17760] in
                                                     uu____17731 ::
                                                       uu____17757
                                                   else [] in
                                                 let g =
                                                   let uu____17765 =
                                                     let uu____17768 =
                                                       let uu____17771 =
                                                         let uu____17774 =
                                                           let uu____17777 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17777 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17774 in
                                                       FStar_List.append
                                                         decls3 uu____17771 in
                                                     FStar_List.append decls2
                                                       uu____17768 in
                                                   FStar_List.append decls11
                                                     uu____17765 in
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
          let uu____17812 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17812 with
          | FStar_Pervasives_Native.None  ->
              let uu____17849 = encode_free_var false env x t t_norm [] in
              (match uu____17849 with
               | (decls,env1) ->
                   let uu____17876 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17876 with
                    | (n1,x',uu____17903) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17924) ->
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
            let uu____17984 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17984 with
            | (decls,env1) ->
                let uu____18003 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____18003
                then
                  let uu____18010 =
                    let uu____18013 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____18013 in
                  (uu____18010, env1)
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
             (fun uu____18068  ->
                fun lb  ->
                  match uu____18068 with
                  | (decls,env1) ->
                      let uu____18088 =
                        let uu____18095 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____18095
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18088 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18117 = FStar_Syntax_Util.head_and_args t in
    match uu____18117 with
    | (hd1,args) ->
        let uu____18154 =
          let uu____18155 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18155.FStar_Syntax_Syntax.n in
        (match uu____18154 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18159,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18178 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18203  ->
      fun quals  ->
        match uu____18203 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18279 = FStar_Util.first_N nbinders formals in
              match uu____18279 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18360  ->
                         fun uu____18361  ->
                           match (uu____18360, uu____18361) with
                           | ((formal,uu____18379),(binder,uu____18381)) ->
                               let uu____18390 =
                                 let uu____18397 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18397) in
                               FStar_Syntax_Syntax.NT uu____18390) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18405 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18436  ->
                              match uu____18436 with
                              | (x,i) ->
                                  let uu____18447 =
                                    let uu___167_18448 = x in
                                    let uu____18449 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___167_18448.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___167_18448.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18449
                                    } in
                                  (uu____18447, i))) in
                    FStar_All.pipe_right uu____18405
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18467 =
                      let uu____18468 = FStar_Syntax_Subst.compress body in
                      let uu____18469 =
                        let uu____18470 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18470 in
                      FStar_Syntax_Syntax.extend_app_n uu____18468
                        uu____18469 in
                    uu____18467 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18531 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18531
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___168_18534 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___168_18534.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___168_18534.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___168_18534.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___168_18534.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___168_18534.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___168_18534.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___168_18534.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___168_18534.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___168_18534.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___168_18534.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___168_18534.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___168_18534.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___168_18534.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___168_18534.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___168_18534.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___168_18534.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___168_18534.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___168_18534.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___168_18534.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___168_18534.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___168_18534.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___168_18534.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___168_18534.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___168_18534.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___168_18534.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___168_18534.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___168_18534.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___168_18534.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___168_18534.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___168_18534.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___168_18534.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___168_18534.FStar_TypeChecker_Env.dsenv)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18567 = FStar_Syntax_Util.abs_formals e in
                match uu____18567 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18631::uu____18632 ->
                         let uu____18647 =
                           let uu____18648 =
                             let uu____18651 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18651 in
                           uu____18648.FStar_Syntax_Syntax.n in
                         (match uu____18647 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18694 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18694 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18736 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18736
                                   then
                                     let uu____18771 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18771 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18865  ->
                                                   fun uu____18866  ->
                                                     match (uu____18865,
                                                             uu____18866)
                                                     with
                                                     | ((x,uu____18884),
                                                        (b,uu____18886)) ->
                                                         let uu____18895 =
                                                           let uu____18902 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18902) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18895)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18904 =
                                            let uu____18925 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18925) in
                                          (uu____18904, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18993 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18993 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19082) ->
                              let uu____19087 =
                                let uu____19108 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19108 in
                              (uu____19087, true)
                          | uu____19173 when Prims.op_Negation norm1 ->
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
                          | uu____19175 ->
                              let uu____19176 =
                                let uu____19177 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19178 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19177
                                  uu____19178 in
                              failwith uu____19176)
                     | uu____19203 ->
                         let uu____19204 =
                           let uu____19205 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19205.FStar_Syntax_Syntax.n in
                         (match uu____19204 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19250 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19250 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19282 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19282 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19365 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19421 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19421
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19433 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19527  ->
                            fun lb  ->
                              match uu____19527 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19622 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19622
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19625 =
                                      let uu____19640 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19640
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19625 with
                                    | (tok,decl,env2) ->
                                        let uu____19686 =
                                          let uu____19699 =
                                            let uu____19710 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19710, tok) in
                                          uu____19699 :: toks in
                                        (uu____19686, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19433 with
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
                        | uu____19893 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19901 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19901 vars)
                            else
                              (let uu____19903 =
                                 let uu____19910 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19910) in
                               FStar_SMTEncoding_Util.mkApp uu____19903) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19992;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19994;
                             FStar_Syntax_Syntax.lbeff = uu____19995;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____20058 =
                              let uu____20065 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____20065 with
                              | (tcenv',uu____20083,e_t) ->
                                  let uu____20089 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20100 -> failwith "Impossible" in
                                  (match uu____20089 with
                                   | (e1,t_norm1) ->
                                       ((let uu___171_20116 = env2 in
                                         {
                                           bindings =
                                             (uu___171_20116.bindings);
                                           depth = (uu___171_20116.depth);
                                           tcenv = tcenv';
                                           warn = (uu___171_20116.warn);
                                           cache = (uu___171_20116.cache);
                                           nolabels =
                                             (uu___171_20116.nolabels);
                                           use_zfuel_name =
                                             (uu___171_20116.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___171_20116.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___171_20116.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____20058 with
                             | (env',e1,t_norm1) ->
                                 let uu____20126 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20126 with
                                  | ((binders,body,uu____20147,uu____20148),curry)
                                      ->
                                      ((let uu____20159 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20159
                                        then
                                          let uu____20160 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20161 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20160 uu____20161
                                        else ());
                                       (let uu____20163 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20163 with
                                        | (vars,guards,env'1,binder_decls,uu____20190)
                                            ->
                                            let body1 =
                                              let uu____20204 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20204
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20207 =
                                              let uu____20216 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20216
                                              then
                                                let uu____20227 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20228 =
                                                  encode_formula body1 env'1 in
                                                (uu____20227, uu____20228)
                                              else
                                                (let uu____20238 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20238)) in
                                            (match uu____20207 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20261 =
                                                     let uu____20268 =
                                                       let uu____20269 =
                                                         let uu____20280 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20280) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20269 in
                                                     let uu____20291 =
                                                       let uu____20294 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20294 in
                                                     (uu____20268,
                                                       uu____20291,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20261 in
                                                 let uu____20297 =
                                                   let uu____20300 =
                                                     let uu____20303 =
                                                       let uu____20306 =
                                                         let uu____20309 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20309 in
                                                       FStar_List.append
                                                         decls2 uu____20306 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20303 in
                                                   FStar_List.append decls1
                                                     uu____20300 in
                                                 (uu____20297, env2))))))
                        | uu____20314 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20399 = varops.fresh "fuel" in
                          (uu____20399, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20402 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20490  ->
                                  fun uu____20491  ->
                                    match (uu____20490, uu____20491) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20639 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20639 in
                                        let gtok =
                                          let uu____20641 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20641 in
                                        let env4 =
                                          let uu____20643 =
                                            let uu____20646 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20646 in
                                          push_free_var env3 flid gtok
                                            uu____20643 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20402 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20802 t_norm
                              uu____20804 =
                              match (uu____20802, uu____20804) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20848;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20849;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20877 =
                                    let uu____20884 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20884 with
                                    | (tcenv',uu____20906,e_t) ->
                                        let uu____20912 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20923 ->
                                              failwith "Impossible" in
                                        (match uu____20912 with
                                         | (e1,t_norm1) ->
                                             ((let uu___172_20939 = env3 in
                                               {
                                                 bindings =
                                                   (uu___172_20939.bindings);
                                                 depth =
                                                   (uu___172_20939.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___172_20939.warn);
                                                 cache =
                                                   (uu___172_20939.cache);
                                                 nolabels =
                                                   (uu___172_20939.nolabels);
                                                 use_zfuel_name =
                                                   (uu___172_20939.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___172_20939.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___172_20939.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20877 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20954 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20954
                                         then
                                           let uu____20955 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20956 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20957 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20955 uu____20956
                                             uu____20957
                                         else ());
                                        (let uu____20959 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20959 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20996 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20996
                                               then
                                                 let uu____20997 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20998 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20999 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____21000 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20997 uu____20998
                                                   uu____20999 uu____21000
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21004 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____21004 with
                                               | (vars,guards,env'1,binder_decls,uu____21035)
                                                   ->
                                                   let decl_g =
                                                     let uu____21049 =
                                                       let uu____21060 =
                                                         let uu____21063 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21063 in
                                                       (g, uu____21060,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21049 in
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
                                                     let uu____21088 =
                                                       let uu____21095 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____21095) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21088 in
                                                   let gsapp =
                                                     let uu____21105 =
                                                       let uu____21112 =
                                                         let uu____21115 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21115 ::
                                                           vars_tm in
                                                       (g, uu____21112) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21105 in
                                                   let gmax =
                                                     let uu____21121 =
                                                       let uu____21128 =
                                                         let uu____21131 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21131 ::
                                                           vars_tm in
                                                       (g, uu____21128) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21121 in
                                                   let body1 =
                                                     let uu____21137 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21137
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21139 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21139 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21157 =
                                                            let uu____21164 =
                                                              let uu____21165
                                                                =
                                                                let uu____21180
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
                                                                  uu____21180) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21165 in
                                                            let uu____21201 =
                                                              let uu____21204
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21204 in
                                                            (uu____21164,
                                                              uu____21201,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21157 in
                                                        let eqn_f =
                                                          let uu____21208 =
                                                            let uu____21215 =
                                                              let uu____21216
                                                                =
                                                                let uu____21227
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21227) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21216 in
                                                            (uu____21215,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21208 in
                                                        let eqn_g' =
                                                          let uu____21241 =
                                                            let uu____21248 =
                                                              let uu____21249
                                                                =
                                                                let uu____21260
                                                                  =
                                                                  let uu____21261
                                                                    =
                                                                    let uu____21266
                                                                    =
                                                                    let uu____21267
                                                                    =
                                                                    let uu____21274
                                                                    =
                                                                    let uu____21277
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21277
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21274) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21267 in
                                                                    (gsapp,
                                                                    uu____21266) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21261 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21260) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21249 in
                                                            (uu____21248,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21241 in
                                                        let uu____21300 =
                                                          let uu____21309 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21309
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21338)
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
                                                                  let uu____21363
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21363
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21368
                                                                  =
                                                                  let uu____21375
                                                                    =
                                                                    let uu____21376
                                                                    =
                                                                    let uu____21387
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21387) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21376 in
                                                                  (uu____21375,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21368 in
                                                              let uu____21408
                                                                =
                                                                let uu____21415
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21415
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21428
                                                                    =
                                                                    let uu____21431
                                                                    =
                                                                    let uu____21432
                                                                    =
                                                                    let uu____21439
                                                                    =
                                                                    let uu____21440
                                                                    =
                                                                    let uu____21451
                                                                    =
                                                                    let uu____21452
                                                                    =
                                                                    let uu____21457
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21457,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21452 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21451) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21440 in
                                                                    (uu____21439,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21432 in
                                                                    [uu____21431] in
                                                                    (d3,
                                                                    uu____21428) in
                                                              (match uu____21408
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21300
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
                            let uu____21522 =
                              let uu____21535 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21614  ->
                                   fun uu____21615  ->
                                     match (uu____21614, uu____21615) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21770 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21770 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21535 in
                            (match uu____21522 with
                             | (decls2,eqns,env01) ->
                                 let uu____21843 =
                                   let isDeclFun uu___138_21855 =
                                     match uu___138_21855 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21856 -> true
                                     | uu____21867 -> false in
                                   let uu____21868 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21868
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21843 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21908 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___139_21912  ->
                                 match uu___139_21912 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21913 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21919 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21919))) in
                      if uu____21908
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
                   let uu____21971 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21971
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
        let uu____22020 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22020 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22024 = encode_sigelt' env se in
      match uu____22024 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22040 =
                  let uu____22041 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22041 in
                [uu____22040]
            | uu____22042 ->
                let uu____22043 =
                  let uu____22046 =
                    let uu____22047 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22047 in
                  uu____22046 :: g in
                let uu____22048 =
                  let uu____22051 =
                    let uu____22052 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22052 in
                  [uu____22051] in
                FStar_List.append uu____22043 uu____22048 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22065 =
          let uu____22066 = FStar_Syntax_Subst.compress t in
          uu____22066.FStar_Syntax_Syntax.n in
        match uu____22065 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22070)) -> s = "opaque_to_smt"
        | uu____22071 -> false in
      let is_uninterpreted_by_smt t =
        let uu____22076 =
          let uu____22077 = FStar_Syntax_Subst.compress t in
          uu____22077.FStar_Syntax_Syntax.n in
        match uu____22076 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22081)) -> s = "uninterpreted_by_smt"
        | uu____22082 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22087 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22092 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22095 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22098 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22113 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22117 =
            let uu____22118 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22118 Prims.op_Negation in
          if uu____22117
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22144 ->
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
               let uu____22164 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22164 with
               | (aname,atok,env2) ->
                   let uu____22180 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22180 with
                    | (formals,uu____22198) ->
                        let uu____22211 =
                          let uu____22216 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22216 env2 in
                        (match uu____22211 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22228 =
                                 let uu____22229 =
                                   let uu____22240 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22256  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22240,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22229 in
                               [uu____22228;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22269 =
                               let aux uu____22321 uu____22322 =
                                 match (uu____22321, uu____22322) with
                                 | ((bv,uu____22374),(env3,acc_sorts,acc)) ->
                                     let uu____22412 = gen_term_var env3 bv in
                                     (match uu____22412 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22269 with
                              | (uu____22484,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22507 =
                                      let uu____22514 =
                                        let uu____22515 =
                                          let uu____22526 =
                                            let uu____22527 =
                                              let uu____22532 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22532) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22527 in
                                          ([[app]], xs_sorts, uu____22526) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22515 in
                                      (uu____22514,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22507 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22552 =
                                      let uu____22559 =
                                        let uu____22560 =
                                          let uu____22571 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22571) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22560 in
                                      (uu____22559,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22552 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22590 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22590 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22618,uu____22619)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22620 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22620 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22637,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22643 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___140_22647  ->
                      match uu___140_22647 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22648 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22653 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22654 -> false)) in
            Prims.op_Negation uu____22643 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22663 =
               let uu____22670 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22670 env fv t quals in
             match uu____22663 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22685 =
                   let uu____22688 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22688 in
                 (uu____22685, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22696 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22696 with
           | (uu____22705,f1) ->
               let uu____22707 = encode_formula f1 env in
               (match uu____22707 with
                | (f2,decls) ->
                    let g =
                      let uu____22721 =
                        let uu____22722 =
                          let uu____22729 =
                            let uu____22732 =
                              let uu____22733 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22733 in
                            FStar_Pervasives_Native.Some uu____22732 in
                          let uu____22734 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22729, uu____22734) in
                        FStar_SMTEncoding_Util.mkAssume uu____22722 in
                      [uu____22721] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22740) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22752 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22770 =
                       let uu____22773 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22773.FStar_Syntax_Syntax.fv_name in
                     uu____22770.FStar_Syntax_Syntax.v in
                   let uu____22774 =
                     let uu____22775 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22775 in
                   if uu____22774
                   then
                     let val_decl =
                       let uu___175_22803 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___175_22803.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___175_22803.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___175_22803.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22808 = encode_sigelt' env1 val_decl in
                     match uu____22808 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22752 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22836,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22838;
                          FStar_Syntax_Syntax.lbtyp = uu____22839;
                          FStar_Syntax_Syntax.lbeff = uu____22840;
                          FStar_Syntax_Syntax.lbdef = uu____22841;_}::[]),uu____22842)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22861 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22861 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22890 =
                   let uu____22893 =
                     let uu____22894 =
                       let uu____22901 =
                         let uu____22902 =
                           let uu____22913 =
                             let uu____22914 =
                               let uu____22919 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22919) in
                             FStar_SMTEncoding_Util.mkEq uu____22914 in
                           ([[b2t_x]], [xx], uu____22913) in
                         FStar_SMTEncoding_Util.mkForall uu____22902 in
                       (uu____22901,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22894 in
                   [uu____22893] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22890 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22952,uu____22953) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___141_22962  ->
                  match uu___141_22962 with
                  | FStar_Syntax_Syntax.Discriminator uu____22963 -> true
                  | uu____22964 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22967,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22978 =
                     let uu____22979 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22979.FStar_Ident.idText in
                   uu____22978 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___142_22983  ->
                     match uu___142_22983 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22984 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22988) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___143_23005  ->
                  match uu___143_23005 with
                  | FStar_Syntax_Syntax.Projector uu____23006 -> true
                  | uu____23011 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23014 = try_lookup_free_var env l in
          (match uu____23014 with
           | FStar_Pervasives_Native.Some uu____23021 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___176_23025 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___176_23025.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___176_23025.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___176_23025.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23032) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23050) ->
          let uu____23059 = encode_sigelts env ses in
          (match uu____23059 with
           | (g,env1) ->
               let uu____23076 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___144_23099  ->
                         match uu___144_23099 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23100;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23101;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23102;_}
                             -> false
                         | uu____23105 -> true)) in
               (match uu____23076 with
                | (g',inversions) ->
                    let uu____23120 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___145_23141  ->
                              match uu___145_23141 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23142 ->
                                  true
                              | uu____23153 -> false)) in
                    (match uu____23120 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23171,tps,k,uu____23174,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___146_23191  ->
                    match uu___146_23191 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23192 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23201 = c in
              match uu____23201 with
              | (name,args,uu____23206,uu____23207,uu____23208) ->
                  let uu____23213 =
                    let uu____23214 =
                      let uu____23225 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23242  ->
                                match uu____23242 with
                                | (uu____23249,sort,uu____23251) -> sort)) in
                      (name, uu____23225, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23214 in
                  [uu____23213]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23278 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23284 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23284 FStar_Option.isNone)) in
            if uu____23278
            then []
            else
              (let uu____23316 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23316 with
               | (xxsym,xx) ->
                   let uu____23325 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23364  ->
                             fun l  ->
                               match uu____23364 with
                               | (out,decls) ->
                                   let uu____23384 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23384 with
                                    | (uu____23395,data_t) ->
                                        let uu____23397 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23397 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23443 =
                                                 let uu____23444 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23444.FStar_Syntax_Syntax.n in
                                               match uu____23443 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23455,indices) ->
                                                   indices
                                               | uu____23477 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23501  ->
                                                         match uu____23501
                                                         with
                                                         | (x,uu____23507) ->
                                                             let uu____23508
                                                               =
                                                               let uu____23509
                                                                 =
                                                                 let uu____23516
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23516,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23509 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23508)
                                                    env) in
                                             let uu____23519 =
                                               encode_args indices env1 in
                                             (match uu____23519 with
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
                                                      let uu____23545 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23561
                                                                 =
                                                                 let uu____23566
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23566,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23561)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23545
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23569 =
                                                      let uu____23570 =
                                                        let uu____23575 =
                                                          let uu____23576 =
                                                            let uu____23581 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23581,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23576 in
                                                        (out, uu____23575) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23570 in
                                                    (uu____23569,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23325 with
                    | (data_ax,decls) ->
                        let uu____23594 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23594 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23605 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23605 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23609 =
                                 let uu____23616 =
                                   let uu____23617 =
                                     let uu____23628 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23643 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23628,
                                       uu____23643) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23617 in
                                 let uu____23658 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23616,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23658) in
                               FStar_SMTEncoding_Util.mkAssume uu____23609 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23661 =
            let uu____23674 =
              let uu____23675 = FStar_Syntax_Subst.compress k in
              uu____23675.FStar_Syntax_Syntax.n in
            match uu____23674 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23720 -> (tps, k) in
          (match uu____23661 with
           | (formals,res) ->
               let uu____23743 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23743 with
                | (formals1,res1) ->
                    let uu____23754 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23754 with
                     | (vars,guards,env',binder_decls,uu____23779) ->
                         let uu____23792 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23792 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23811 =
                                  let uu____23818 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23818) in
                                FStar_SMTEncoding_Util.mkApp uu____23811 in
                              let uu____23827 =
                                let tname_decl =
                                  let uu____23837 =
                                    let uu____23838 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23870  ->
                                              match uu____23870 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23883 = varops.next_id () in
                                    (tname, uu____23838,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23883, false) in
                                  constructor_or_logic_type_decl uu____23837 in
                                let uu____23892 =
                                  match vars with
                                  | [] ->
                                      let uu____23905 =
                                        let uu____23906 =
                                          let uu____23909 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23909 in
                                        push_free_var env1 t tname
                                          uu____23906 in
                                      ([], uu____23905)
                                  | uu____23916 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23925 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23925 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23939 =
                                          let uu____23946 =
                                            let uu____23947 =
                                              let uu____23962 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23962) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23947 in
                                          (uu____23946,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23939 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23892 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23827 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24002 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24002 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24020 =
                                               let uu____24021 =
                                                 let uu____24028 =
                                                   let uu____24029 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24029 in
                                                 (uu____24028,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24021 in
                                             [uu____24020]
                                           else [] in
                                         let uu____24033 =
                                           let uu____24036 =
                                             let uu____24039 =
                                               let uu____24040 =
                                                 let uu____24047 =
                                                   let uu____24048 =
                                                     let uu____24059 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24059) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24048 in
                                                 (uu____24047,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24040 in
                                             [uu____24039] in
                                           FStar_List.append karr uu____24036 in
                                         FStar_List.append decls1 uu____24033 in
                                   let aux =
                                     let uu____24075 =
                                       let uu____24078 =
                                         inversion_axioms tapp vars in
                                       let uu____24081 =
                                         let uu____24084 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24084] in
                                       FStar_List.append uu____24078
                                         uu____24081 in
                                     FStar_List.append kindingAx uu____24075 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24091,uu____24092,uu____24093,uu____24094,uu____24095)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24103,t,uu____24105,n_tps,uu____24107) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24115 = new_term_constant_and_tok_from_lid env d in
          (match uu____24115 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24132 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24132 with
                | (formals,t_res) ->
                    let uu____24167 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24167 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24181 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24181 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24251 =
                                            mk_term_projector_name d x in
                                          (uu____24251,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24253 =
                                  let uu____24272 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24272, true) in
                                FStar_All.pipe_right uu____24253
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
                              let uu____24311 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24311 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24323::uu____24324 ->
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
                                         let uu____24369 =
                                           let uu____24380 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24380) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24369
                                     | uu____24405 -> tok_typing in
                                   let uu____24414 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24414 with
                                    | (vars',guards',env'',decls_formals,uu____24439)
                                        ->
                                        let uu____24452 =
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
                                        (match uu____24452 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24483 ->
                                                   let uu____24490 =
                                                     let uu____24491 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24491 in
                                                   [uu____24490] in
                                             let encode_elim uu____24501 =
                                               let uu____24502 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24502 with
                                               | (head1,args) ->
                                                   let uu____24545 =
                                                     let uu____24546 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24546.FStar_Syntax_Syntax.n in
                                                   (match uu____24545 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24556;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24557;_},uu____24558)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24564 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24564
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
                                                                 | uu____24607
                                                                    ->
                                                                    let uu____24608
                                                                    =
                                                                    let uu____24609
                                                                    =
                                                                    let uu____24614
                                                                    =
                                                                    let uu____24615
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24615 in
                                                                    (uu____24614,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24609 in
                                                                    FStar_Exn.raise
                                                                    uu____24608 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24631
                                                                    =
                                                                    let uu____24632
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24632 in
                                                                    if
                                                                    uu____24631
                                                                    then
                                                                    let uu____24645
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24645]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24647
                                                               =
                                                               let uu____24660
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24710
                                                                     ->
                                                                    fun
                                                                    uu____24711
                                                                     ->
                                                                    match 
                                                                    (uu____24710,
                                                                    uu____24711)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24806
                                                                    =
                                                                    let uu____24813
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24813 in
                                                                    (match uu____24806
                                                                    with
                                                                    | 
                                                                    (uu____24826,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24834
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24834
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24836
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24836
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
                                                                 uu____24660 in
                                                             (match uu____24647
                                                              with
                                                              | (uu____24851,arg_vars,elim_eqns_or_guards,uu____24854)
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
                                                                    let uu____24884
                                                                    =
                                                                    let uu____24891
                                                                    =
                                                                    let uu____24892
                                                                    =
                                                                    let uu____24903
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24914
                                                                    =
                                                                    let uu____24915
                                                                    =
                                                                    let uu____24920
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24920) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24915 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24903,
                                                                    uu____24914) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24892 in
                                                                    (uu____24891,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24884 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24943
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24943,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24945
                                                                    =
                                                                    let uu____24952
                                                                    =
                                                                    let uu____24953
                                                                    =
                                                                    let uu____24964
                                                                    =
                                                                    let uu____24969
                                                                    =
                                                                    let uu____24972
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24972] in
                                                                    [uu____24969] in
                                                                    let uu____24977
                                                                    =
                                                                    let uu____24978
                                                                    =
                                                                    let uu____24983
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24984
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24983,
                                                                    uu____24984) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24978 in
                                                                    (uu____24964,
                                                                    [x],
                                                                    uu____24977) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24953 in
                                                                    let uu____25003
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24952,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25003) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24945
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25010
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
                                                                    (let uu____25038
                                                                    =
                                                                    let uu____25039
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25039
                                                                    dapp1 in
                                                                    [uu____25038]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25010
                                                                    FStar_List.flatten in
                                                                    let uu____25046
                                                                    =
                                                                    let uu____25053
                                                                    =
                                                                    let uu____25054
                                                                    =
                                                                    let uu____25065
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25076
                                                                    =
                                                                    let uu____25077
                                                                    =
                                                                    let uu____25082
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25082) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25077 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25065,
                                                                    uu____25076) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25054 in
                                                                    (uu____25053,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25046) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25103 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25103
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
                                                                 | uu____25146
                                                                    ->
                                                                    let uu____25147
                                                                    =
                                                                    let uu____25148
                                                                    =
                                                                    let uu____25153
                                                                    =
                                                                    let uu____25154
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25154 in
                                                                    (uu____25153,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25148 in
                                                                    FStar_Exn.raise
                                                                    uu____25147 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25171
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25171 in
                                                                    if
                                                                    uu____25170
                                                                    then
                                                                    let uu____25184
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25184]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25186
                                                               =
                                                               let uu____25199
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25249
                                                                     ->
                                                                    fun
                                                                    uu____25250
                                                                     ->
                                                                    match 
                                                                    (uu____25249,
                                                                    uu____25250)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25345
                                                                    =
                                                                    let uu____25352
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25352 in
                                                                    (match uu____25345
                                                                    with
                                                                    | 
                                                                    (uu____25365,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25373
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25373
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25375
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25375
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
                                                                 uu____25199 in
                                                             (match uu____25186
                                                              with
                                                              | (uu____25390,arg_vars,elim_eqns_or_guards,uu____25393)
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
                                                                    let uu____25423
                                                                    =
                                                                    let uu____25430
                                                                    =
                                                                    let uu____25431
                                                                    =
                                                                    let uu____25442
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25453
                                                                    =
                                                                    let uu____25454
                                                                    =
                                                                    let uu____25459
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25459) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25454 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25442,
                                                                    uu____25453) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25431 in
                                                                    (uu____25430,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25423 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25482
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25482,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25484
                                                                    =
                                                                    let uu____25491
                                                                    =
                                                                    let uu____25492
                                                                    =
                                                                    let uu____25503
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25511
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25511] in
                                                                    [uu____25508] in
                                                                    let uu____25516
                                                                    =
                                                                    let uu____25517
                                                                    =
                                                                    let uu____25522
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25523
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25522,
                                                                    uu____25523) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25517 in
                                                                    (uu____25503,
                                                                    [x],
                                                                    uu____25516) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25492 in
                                                                    let uu____25542
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25491,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25542) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25484
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25549
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
                                                                    (let uu____25577
                                                                    =
                                                                    let uu____25578
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25578
                                                                    dapp1 in
                                                                    [uu____25577]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25549
                                                                    FStar_List.flatten in
                                                                    let uu____25585
                                                                    =
                                                                    let uu____25592
                                                                    =
                                                                    let uu____25593
                                                                    =
                                                                    let uu____25604
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25615
                                                                    =
                                                                    let uu____25616
                                                                    =
                                                                    let uu____25621
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25621) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25616 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25604,
                                                                    uu____25615) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25593 in
                                                                    (uu____25592,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25585) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25640 ->
                                                        ((let uu____25642 =
                                                            let uu____25643 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25644 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25643
                                                              uu____25644 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25642);
                                                         ([], []))) in
                                             let uu____25649 = encode_elim () in
                                             (match uu____25649 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25669 =
                                                      let uu____25672 =
                                                        let uu____25675 =
                                                          let uu____25678 =
                                                            let uu____25681 =
                                                              let uu____25682
                                                                =
                                                                let uu____25693
                                                                  =
                                                                  let uu____25696
                                                                    =
                                                                    let uu____25697
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25697 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25696 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25693) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25682 in
                                                            [uu____25681] in
                                                          let uu____25702 =
                                                            let uu____25705 =
                                                              let uu____25708
                                                                =
                                                                let uu____25711
                                                                  =
                                                                  let uu____25714
                                                                    =
                                                                    let uu____25717
                                                                    =
                                                                    let uu____25720
                                                                    =
                                                                    let uu____25721
                                                                    =
                                                                    let uu____25728
                                                                    =
                                                                    let uu____25729
                                                                    =
                                                                    let uu____25740
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25740) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25729 in
                                                                    (uu____25728,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25721 in
                                                                    let uu____25753
                                                                    =
                                                                    let uu____25756
                                                                    =
                                                                    let uu____25757
                                                                    =
                                                                    let uu____25764
                                                                    =
                                                                    let uu____25765
                                                                    =
                                                                    let uu____25776
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25787
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25776,
                                                                    uu____25787) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25765 in
                                                                    (uu____25764,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25757 in
                                                                    [uu____25756] in
                                                                    uu____25720
                                                                    ::
                                                                    uu____25753 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25717 in
                                                                  FStar_List.append
                                                                    uu____25714
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25711 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25708 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25705 in
                                                          FStar_List.append
                                                            uu____25678
                                                            uu____25702 in
                                                        FStar_List.append
                                                          decls3 uu____25675 in
                                                      FStar_List.append
                                                        decls2 uu____25672 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25669 in
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
           (fun uu____25833  ->
              fun se  ->
                match uu____25833 with
                | (g,env1) ->
                    let uu____25853 = encode_sigelt env1 se in
                    (match uu____25853 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25912 =
        match uu____25912 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25944 ->
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
                 ((let uu____25950 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25950
                   then
                     let uu____25951 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25952 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25953 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25951 uu____25952 uu____25953
                   else ());
                  (let uu____25955 = encode_term t1 env1 in
                   match uu____25955 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25971 =
                         let uu____25978 =
                           let uu____25979 =
                             let uu____25980 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25980
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25979 in
                         new_term_constant_from_string env1 x uu____25978 in
                       (match uu____25971 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25996 = FStar_Options.log_queries () in
                              if uu____25996
                              then
                                let uu____25999 =
                                  let uu____26000 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26001 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26002 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26000 uu____26001 uu____26002 in
                                FStar_Pervasives_Native.Some uu____25999
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26018,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26032 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____26032 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26055,se,uu____26057) ->
                 let uu____26062 = encode_sigelt env1 se in
                 (match uu____26062 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26079,se) ->
                 let uu____26085 = encode_sigelt env1 se in
                 (match uu____26085 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26102 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26102 with | (uu____26125,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26140 'Auu____26141 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26141,'Auu____26140)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26209  ->
              match uu____26209 with
              | (l,uu____26221,uu____26222) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26268  ->
              match uu____26268 with
              | (l,uu____26282,uu____26283) ->
                  let uu____26292 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26293 =
                    let uu____26296 =
                      let uu____26297 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26297 in
                    [uu____26296] in
                  uu____26292 :: uu____26293)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26319 =
      let uu____26322 =
        let uu____26323 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26326 =
          let uu____26327 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26327 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26323;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26326
        } in
      [uu____26322] in
    FStar_ST.op_Colon_Equals last_env uu____26319
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26386 = FStar_ST.op_Bang last_env in
      match uu____26386 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26440 ->
          let uu___177_26443 = e in
          let uu____26444 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___177_26443.bindings);
            depth = (uu___177_26443.depth);
            tcenv;
            warn = (uu___177_26443.warn);
            cache = (uu___177_26443.cache);
            nolabels = (uu___177_26443.nolabels);
            use_zfuel_name = (uu___177_26443.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___177_26443.encode_non_total_function_typ);
            current_module_name = uu____26444
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26449 = FStar_ST.op_Bang last_env in
    match uu____26449 with
    | [] -> failwith "Empty env stack"
    | uu____26502::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26559  ->
    let uu____26560 = FStar_ST.op_Bang last_env in
    match uu____26560 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___178_26621 = hd1 in
          {
            bindings = (uu___178_26621.bindings);
            depth = (uu___178_26621.depth);
            tcenv = (uu___178_26621.tcenv);
            warn = (uu___178_26621.warn);
            cache = refs;
            nolabels = (uu___178_26621.nolabels);
            use_zfuel_name = (uu___178_26621.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___178_26621.encode_non_total_function_typ);
            current_module_name = (uu___178_26621.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26675  ->
    let uu____26676 = FStar_ST.op_Bang last_env in
    match uu____26676 with
    | [] -> failwith "Popping an empty stack"
    | uu____26729::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26827::uu____26828,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___179_26836 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___179_26836.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___179_26836.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___179_26836.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26837 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26854 =
        let uu____26857 =
          let uu____26858 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26858 in
        let uu____26859 = open_fact_db_tags env in uu____26857 :: uu____26859 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26854
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
      let uu____26883 = encode_sigelt env se in
      match uu____26883 with
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
        let uu____26921 = FStar_Options.log_queries () in
        if uu____26921
        then
          let uu____26924 =
            let uu____26925 =
              let uu____26926 =
                let uu____26927 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26927 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26926 in
            FStar_SMTEncoding_Term.Caption uu____26925 in
          uu____26924 :: decls
        else decls in
      let env =
        let uu____26938 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26938 tcenv in
      let uu____26939 = encode_top_level_facts env se in
      match uu____26939 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26953 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26953))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26967 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26967
       then
         let uu____26968 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26968
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27003  ->
                 fun se  ->
                   match uu____27003 with
                   | (g,env2) ->
                       let uu____27023 = encode_top_level_facts env2 se in
                       (match uu____27023 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27046 =
         encode_signature
           (let uu___180_27055 = env in
            {
              bindings = (uu___180_27055.bindings);
              depth = (uu___180_27055.depth);
              tcenv = (uu___180_27055.tcenv);
              warn = false;
              cache = (uu___180_27055.cache);
              nolabels = (uu___180_27055.nolabels);
              use_zfuel_name = (uu___180_27055.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___180_27055.encode_non_total_function_typ);
              current_module_name = (uu___180_27055.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27046 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27072 = FStar_Options.log_queries () in
             if uu____27072
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___181_27080 = env1 in
               {
                 bindings = (uu___181_27080.bindings);
                 depth = (uu___181_27080.depth);
                 tcenv = (uu___181_27080.tcenv);
                 warn = true;
                 cache = (uu___181_27080.cache);
                 nolabels = (uu___181_27080.nolabels);
                 use_zfuel_name = (uu___181_27080.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___181_27080.encode_non_total_function_typ);
                 current_module_name = (uu___181_27080.current_module_name)
               });
            (let uu____27082 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27082
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
        (let uu____27137 =
           let uu____27138 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27138.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27137);
        (let env =
           let uu____27140 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27140 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27152 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27187 = aux rest in
                 (match uu____27187 with
                  | (out,rest1) ->
                      let t =
                        let uu____27217 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27217 with
                        | FStar_Pervasives_Native.Some uu____27222 ->
                            let uu____27223 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27223
                              x.FStar_Syntax_Syntax.sort
                        | uu____27224 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27228 =
                        let uu____27231 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___182_27234 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___182_27234.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___182_27234.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27231 :: out in
                      (uu____27228, rest1))
             | uu____27239 -> ([], bindings1) in
           let uu____27246 = aux bindings in
           match uu____27246 with
           | (closing,bindings1) ->
               let uu____27271 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27271, bindings1) in
         match uu____27152 with
         | (q1,bindings1) ->
             let uu____27294 =
               let uu____27299 =
                 FStar_List.filter
                   (fun uu___147_27304  ->
                      match uu___147_27304 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27305 ->
                          false
                      | uu____27312 -> true) bindings1 in
               encode_env_bindings env uu____27299 in
             (match uu____27294 with
              | (env_decls,env1) ->
                  ((let uu____27330 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27330
                    then
                      let uu____27331 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27331
                    else ());
                   (let uu____27333 = encode_formula q1 env1 in
                    match uu____27333 with
                    | (phi,qdecls) ->
                        let uu____27354 =
                          let uu____27359 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27359 phi in
                        (match uu____27354 with
                         | (labels,phi1) ->
                             let uu____27376 = encode_labels labels in
                             (match uu____27376 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27413 =
                                      let uu____27420 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27421 =
                                        varops.mk_unique "@query" in
                                      (uu____27420,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27421) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27413 in
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
        let uu____27440 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27440 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27442 = encode_formula q env in
       match uu____27442 with
       | (f,uu____27448) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27450) -> true
             | uu____27455 -> false)))