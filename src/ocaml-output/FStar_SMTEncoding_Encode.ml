
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
          (fun uu____883  ->
             match uu____883 with
             | (names1,uu____895) -> FStar_Util.smap_try_find names1 y1) in
      match uu____794 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____904 ->
          (FStar_Util.incr ctr;
           (let uu____927 =
              let uu____928 =
                let uu____929 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____929 in
              Prims.strcat "__" uu____928 in
            Prims.strcat y1 uu____927)) in
    let top_scope =
      let uu____957 =
        let uu____966 = FStar_ST.op_Bang scopes in FStar_List.hd uu____966 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____957 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1078 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1129 =
      let uu____1130 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1130 in
    FStar_Util.format2 "%s_%s" pfx uu____1129 in
  let string_const s =
    let uu____1135 =
      let uu____1138 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1138
        (fun uu____1224  ->
           match uu____1224 with
           | (uu____1235,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1135 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1248 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1248 in
        let top_scope =
          let uu____1252 =
            let uu____1261 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1261 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1252 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1362 =
    let uu____1363 =
      let uu____1374 = new_scope () in
      let uu____1383 = FStar_ST.op_Bang scopes in uu____1374 :: uu____1383 in
    FStar_ST.op_Colon_Equals scopes uu____1363 in
  let pop1 uu____1533 =
    let uu____1534 =
      let uu____1545 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1545 in
    FStar_ST.op_Colon_Equals scopes uu____1534 in
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
    let uu___133_1696 = x in
    let uu____1697 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1697;
      FStar_Syntax_Syntax.index = (uu___133_1696.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___133_1696.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1731 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1769 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____1820 'Auu____1821 .
    'Auu____1821 ->
      ('Auu____1821,'Auu____1820 FStar_Pervasives_Native.option)
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
  'Auu____2135 .
    'Auu____2135 ->
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
                 (fun uu___109_2169  ->
                    match uu___109_2169 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2173 -> [])) in
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
    let uu____2184 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___110_2194  ->
              match uu___110_2194 with
              | Binding_var (x,uu____2196) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2198,uu____2199,uu____2200) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2184 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2217 .
    env_t ->
      (binding -> 'Auu____2217 FStar_Pervasives_Native.option) ->
        'Auu____2217 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2247 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2247
      then
        let uu____2250 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2250
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
      let uu____2265 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2265)
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
        (let uu___134_2283 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___134_2283.tcenv);
           warn = (uu___134_2283.warn);
           cache = (uu___134_2283.cache);
           nolabels = (uu___134_2283.nolabels);
           use_zfuel_name = (uu___134_2283.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___134_2283.encode_non_total_function_typ);
           current_module_name = (uu___134_2283.current_module_name)
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
        (let uu___135_2303 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___135_2303.depth);
           tcenv = (uu___135_2303.tcenv);
           warn = (uu___135_2303.warn);
           cache = (uu___135_2303.cache);
           nolabels = (uu___135_2303.nolabels);
           use_zfuel_name = (uu___135_2303.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___135_2303.encode_non_total_function_typ);
           current_module_name = (uu___135_2303.current_module_name)
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
          (let uu___136_2327 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___136_2327.depth);
             tcenv = (uu___136_2327.tcenv);
             warn = (uu___136_2327.warn);
             cache = (uu___136_2327.cache);
             nolabels = (uu___136_2327.nolabels);
             use_zfuel_name = (uu___136_2327.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___136_2327.encode_non_total_function_typ);
             current_module_name = (uu___136_2327.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___137_2340 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___137_2340.depth);
          tcenv = (uu___137_2340.tcenv);
          warn = (uu___137_2340.warn);
          cache = (uu___137_2340.cache);
          nolabels = (uu___137_2340.nolabels);
          use_zfuel_name = (uu___137_2340.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___137_2340.encode_non_total_function_typ);
          current_module_name = (uu___137_2340.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___111_2366  ->
             match uu___111_2366 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2379 -> FStar_Pervasives_Native.None) in
      let uu____2384 = aux a in
      match uu____2384 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2396 = aux a2 in
          (match uu____2396 with
           | FStar_Pervasives_Native.None  ->
               let uu____2407 =
                 let uu____2408 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2409 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2408 uu____2409 in
               failwith uu____2407
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
      let uu____2438 =
        let uu___138_2439 = env in
        let uu____2440 =
          let uu____2443 =
            let uu____2444 =
              let uu____2457 =
                let uu____2460 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2460 in
              (x, fname, uu____2457, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2444 in
          uu____2443 :: (env.bindings) in
        {
          bindings = uu____2440;
          depth = (uu___138_2439.depth);
          tcenv = (uu___138_2439.tcenv);
          warn = (uu___138_2439.warn);
          cache = (uu___138_2439.cache);
          nolabels = (uu___138_2439.nolabels);
          use_zfuel_name = (uu___138_2439.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___138_2439.encode_non_total_function_typ);
          current_module_name = (uu___138_2439.current_module_name)
        } in
      (fname, ftok, uu____2438)
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
        (fun uu___112_2504  ->
           match uu___112_2504 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2543 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2562 =
        lookup_binding env
          (fun uu___113_2570  ->
             match uu___113_2570 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2585 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2562 FStar_Option.isSome
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
      let uu____2606 = try_lookup_lid env a in
      match uu____2606 with
      | FStar_Pervasives_Native.None  ->
          let uu____2639 =
            let uu____2640 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2640 in
          failwith uu____2639
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
          let uu___139_2692 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___139_2692.depth);
            tcenv = (uu___139_2692.tcenv);
            warn = (uu___139_2692.warn);
            cache = (uu___139_2692.cache);
            nolabels = (uu___139_2692.nolabels);
            use_zfuel_name = (uu___139_2692.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___139_2692.encode_non_total_function_typ);
            current_module_name = (uu___139_2692.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2709 = lookup_lid env x in
        match uu____2709 with
        | (t1,t2,uu____2722) ->
            let t3 =
              let uu____2732 =
                let uu____2739 =
                  let uu____2742 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2742] in
                (f, uu____2739) in
              FStar_SMTEncoding_Util.mkApp uu____2732 in
            let uu___140_2747 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___140_2747.depth);
              tcenv = (uu___140_2747.tcenv);
              warn = (uu___140_2747.warn);
              cache = (uu___140_2747.cache);
              nolabels = (uu___140_2747.nolabels);
              use_zfuel_name = (uu___140_2747.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___140_2747.encode_non_total_function_typ);
              current_module_name = (uu___140_2747.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2762 = try_lookup_lid env l in
      match uu____2762 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2811 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2819,fuel::[]) ->
                         let uu____2823 =
                           let uu____2824 =
                             let uu____2825 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2825
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2824 "fuel" in
                         if uu____2823
                         then
                           let uu____2828 =
                             let uu____2829 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2829
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____2828
                         else FStar_Pervasives_Native.Some t
                     | uu____2833 -> FStar_Pervasives_Native.Some t)
                | uu____2834 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2849 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2849 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2853 =
            let uu____2854 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2854 in
          failwith uu____2853
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2867 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2867 with | (x,uu____2879,uu____2880) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2907 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2907 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2943;
                 FStar_SMTEncoding_Term.rng = uu____2944;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2959 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2983 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___114_3001  ->
           match uu___114_3001 with
           | Binding_fvar (uu____3004,nm',tok,uu____3007) when nm = nm' ->
               tok
           | uu____3016 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3023 .
    'Auu____3023 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3041  ->
      match uu____3041 with
      | (pats,vars,body) ->
          let fallback uu____3066 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3071 = FStar_Options.unthrottle_inductives () in
          if uu____3071
          then fallback ()
          else
            (let uu____3073 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3073 with
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
                           | uu____3104 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3125 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3125
                         | uu____3128 ->
                             let uu____3129 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3129 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3134 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3178 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3191 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3198 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3199 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3216 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3233 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3235 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3235 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3253;
             FStar_Syntax_Syntax.vars = uu____3254;_},uu____3255)
          ->
          let uu____3276 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3276 FStar_Option.isNone
      | uu____3293 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3302 =
        let uu____3303 = FStar_Syntax_Util.un_uinst t in
        uu____3303.FStar_Syntax_Syntax.n in
      match uu____3302 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3306,uu____3307,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___115_3328  ->
                  match uu___115_3328 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3329 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3331 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3331 FStar_Option.isSome
      | uu____3348 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3357 = head_normal env t in
      if uu____3357
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
    let uu____3371 =
      let uu____3372 = FStar_Syntax_Syntax.null_binder t in [uu____3372] in
    let uu____3373 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3371 uu____3373 FStar_Pervasives_Native.None
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
                    let uu____3413 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3413
                | s ->
                    let uu____3418 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3418) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___116_3436  ->
    match uu___116_3436 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3437 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3476;
                       FStar_SMTEncoding_Term.rng = uu____3477;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3500) ->
              let uu____3509 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3520 -> false) args (FStar_List.rev xs)) in
              if uu____3509
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3524,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3528 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3532 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3532)) in
              if uu____3528
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3536 -> FStar_Pervasives_Native.None in
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
    | uu____3766 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3771 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___117_3775  ->
    match uu___117_3775 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____3777 =
          let uu____3784 =
            let uu____3787 =
              let uu____3788 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____3788 in
            [uu____3787] in
          ("FStar.Char.Char", uu____3784) in
        FStar_SMTEncoding_Util.mkApp uu____3777
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____3802 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____3802
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____3804) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (s,uu____3820) -> varops.string_const s
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____3823 =
          let uu____3824 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____3824 in
        failwith uu____3823
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3845 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3858 ->
            let uu____3865 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3865
        | uu____3866 ->
            if norm1
            then let uu____3867 = whnf env t1 in aux false uu____3867
            else
              (let uu____3869 =
                 let uu____3870 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3871 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3870 uu____3871 in
               failwith uu____3869) in
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
    | uu____3903 ->
        let uu____3904 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3904)
let is_arithmetic_primitive:
  'Auu____3921 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3921 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3941::uu____3942::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3946::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3949 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3971 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3987 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____3994 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3994)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4033)::uu____4034::uu____4035::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4086)::uu____4087::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4124 -> false
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
        (let uu____4333 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4333
         then
           let uu____4334 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4334
         else ());
        (let uu____4336 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4420  ->
                   fun b  ->
                     match uu____4420 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4499 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4515 = gen_term_var env1 x in
                           match uu____4515 with
                           | (xxsym,xx,env') ->
                               let uu____4539 =
                                 let uu____4544 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4544 env1 xx in
                               (match uu____4539 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4499 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4336 with
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
          let uu____4703 = encode_term t env in
          match uu____4703 with
          | (t1,decls) ->
              let uu____4714 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4714, decls)
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
          let uu____4725 = encode_term t env in
          match uu____4725 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4740 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4740, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4742 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4742, decls))
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
        let uu____4748 = encode_args args_e env in
        match uu____4748 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4767 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4776 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4776 in
            let binary arg_tms1 =
              let uu____4789 =
                let uu____4790 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4790 in
              let uu____4791 =
                let uu____4792 =
                  let uu____4793 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4793 in
                FStar_SMTEncoding_Term.unboxInt uu____4792 in
              (uu____4789, uu____4791) in
            let mk_default uu____4799 =
              let uu____4800 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4800 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4851 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4851
              then
                let uu____4852 = let uu____4853 = mk_args ts in op uu____4853 in
                FStar_All.pipe_right uu____4852 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4882 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4882
              then
                let uu____4883 = binary ts in
                match uu____4883 with
                | (t1,t2) ->
                    let uu____4890 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4890
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4894 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4894
                 then
                   let uu____4895 = op (binary ts) in
                   FStar_All.pipe_right uu____4895
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
            let uu____5026 =
              let uu____5035 =
                FStar_List.tryFind
                  (fun uu____5057  ->
                     match uu____5057 with
                     | (l,uu____5067) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5035 FStar_Util.must in
            (match uu____5026 with
             | (uu____5106,op) ->
                 let uu____5116 = op arg_tms in (uu____5116, decls))
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
        let uu____5124 = FStar_List.hd args_e in
        match uu____5124 with
        | (tm_sz,uu____5132) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5142 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5142 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5150 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5150);
                   t_decls) in
            let uu____5151 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5171::(sz_arg,uu____5173)::uu____5174::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5223 =
                    let uu____5226 = FStar_List.tail args_e in
                    FStar_List.tail uu____5226 in
                  let uu____5229 =
                    let uu____5232 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5232 in
                  (uu____5223, uu____5229)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5238::(sz_arg,uu____5240)::uu____5241::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5290 =
                    let uu____5291 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5291 in
                  failwith uu____5290
              | uu____5300 ->
                  let uu____5307 = FStar_List.tail args_e in
                  (uu____5307, FStar_Pervasives_Native.None) in
            (match uu____5151 with
             | (arg_tms,ext_sz) ->
                 let uu____5330 = encode_args arg_tms env in
                 (match uu____5330 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5351 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5360 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5360 in
                      let unary_arith arg_tms2 =
                        let uu____5369 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5369 in
                      let binary arg_tms2 =
                        let uu____5382 =
                          let uu____5383 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5383 in
                        let uu____5384 =
                          let uu____5385 =
                            let uu____5386 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5386 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5385 in
                        (uu____5382, uu____5384) in
                      let binary_arith arg_tms2 =
                        let uu____5401 =
                          let uu____5402 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5402 in
                        let uu____5403 =
                          let uu____5404 =
                            let uu____5405 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5405 in
                          FStar_SMTEncoding_Term.unboxInt uu____5404 in
                        (uu____5401, uu____5403) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5454 =
                          let uu____5455 = mk_args ts in op uu____5455 in
                        FStar_All.pipe_right uu____5454 resBox in
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
                        let uu____5545 =
                          let uu____5548 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5548 in
                        let uu____5550 =
                          let uu____5553 =
                            let uu____5554 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5554 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5553 in
                        mk_bv uu____5545 unary uu____5550 arg_tms2 in
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
                      let uu____5729 =
                        let uu____5738 =
                          FStar_List.tryFind
                            (fun uu____5760  ->
                               match uu____5760 with
                               | (l,uu____5770) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5738 FStar_Util.must in
                      (match uu____5729 with
                       | (uu____5811,op) ->
                           let uu____5821 = op arg_tms1 in
                           (uu____5821, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5832 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5832
       then
         let uu____5833 = FStar_Syntax_Print.tag_of_term t in
         let uu____5834 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5835 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5833 uu____5834
           uu____5835
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5841 ->
           let uu____5866 =
             let uu____5867 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5868 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5869 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5870 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5867
               uu____5868 uu____5869 uu____5870 in
           failwith uu____5866
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5875 =
             let uu____5876 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5877 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5878 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5879 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5876
               uu____5877 uu____5878 uu____5879 in
           failwith uu____5875
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5885 =
             let uu____5886 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5886 in
           failwith uu____5885
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____5893) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5935) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5945 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____5945, [])
       | FStar_Syntax_Syntax.Tm_type uu____5948 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5952) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____5958 = encode_const c in (uu____5958, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____5980 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____5980 with
            | (binders1,res) ->
                let uu____5991 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____5991
                then
                  let uu____5996 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____5996 with
                   | (vars,guards,env',decls,uu____6021) ->
                       let fsym =
                         let uu____6039 = varops.fresh "f" in
                         (uu____6039, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6042 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___141_6051 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___141_6051.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___141_6051.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___141_6051.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___141_6051.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___141_6051.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___141_6051.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___141_6051.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___141_6051.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___141_6051.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___141_6051.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___141_6051.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___141_6051.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___141_6051.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___141_6051.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___141_6051.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___141_6051.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___141_6051.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___141_6051.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___141_6051.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___141_6051.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___141_6051.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.type_of =
                                (uu___141_6051.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___141_6051.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___141_6051.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___141_6051.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___141_6051.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___141_6051.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___141_6051.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___141_6051.FStar_TypeChecker_Env.identifier_info)
                            }) res in
                       (match uu____6042 with
                        | (pre_opt,res_t) ->
                            let uu____6062 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6062 with
                             | (res_pred,decls') ->
                                 let uu____6073 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6086 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6086, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6090 =
                                         encode_formula pre env' in
                                       (match uu____6090 with
                                        | (guard,decls0) ->
                                            let uu____6103 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6103, decls0)) in
                                 (match uu____6073 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6115 =
                                          let uu____6126 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6126) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6115 in
                                      let cvars =
                                        let uu____6144 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6144
                                          (FStar_List.filter
                                             (fun uu____6158  ->
                                                match uu____6158 with
                                                | (x,uu____6164) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6183 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6183 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6191 =
                                             let uu____6192 =
                                               let uu____6199 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6199) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6192 in
                                           (uu____6191,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6219 =
                                               let uu____6220 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6220 in
                                             varops.mk_unique uu____6219 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6231 =
                                               FStar_Options.log_queries () in
                                             if uu____6231
                                             then
                                               let uu____6234 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6234
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6242 =
                                               let uu____6249 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6249) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6242 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6261 =
                                               let uu____6268 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6268,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6261 in
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
                                             let uu____6289 =
                                               let uu____6296 =
                                                 let uu____6297 =
                                                   let uu____6308 =
                                                     let uu____6309 =
                                                       let uu____6314 =
                                                         let uu____6315 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6315 in
                                                       (f_has_t, uu____6314) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6309 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6308) in
                                                 mkForall_fuel uu____6297 in
                                               (uu____6296,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6289 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6338 =
                                               let uu____6345 =
                                                 let uu____6346 =
                                                   let uu____6357 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6357) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6346 in
                                               (uu____6345,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6338 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6382 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6382);
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
                     let uu____6397 =
                       let uu____6404 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6404,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6397 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6416 =
                       let uu____6423 =
                         let uu____6424 =
                           let uu____6435 =
                             let uu____6436 =
                               let uu____6441 =
                                 let uu____6442 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6442 in
                               (f_has_t, uu____6441) in
                             FStar_SMTEncoding_Util.mkImp uu____6436 in
                           ([[f_has_t]], [fsym], uu____6435) in
                         mkForall_fuel uu____6424 in
                       (uu____6423, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6416 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6469 ->
           let uu____6476 =
             let uu____6481 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6481 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6488;
                 FStar_Syntax_Syntax.vars = uu____6489;_} ->
                 let uu____6496 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6496 with
                  | (b,f1) ->
                      let uu____6521 =
                        let uu____6522 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6522 in
                      (uu____6521, f1))
             | uu____6531 -> failwith "impossible" in
           (match uu____6476 with
            | (x,f) ->
                let uu____6542 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6542 with
                 | (base_t,decls) ->
                     let uu____6553 = gen_term_var env x in
                     (match uu____6553 with
                      | (x1,xtm,env') ->
                          let uu____6567 = encode_formula f env' in
                          (match uu____6567 with
                           | (refinement,decls') ->
                               let uu____6578 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6578 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6594 =
                                        let uu____6597 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6604 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6597
                                          uu____6604 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6594 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6637  ->
                                              match uu____6637 with
                                              | (y,uu____6643) ->
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
                                    let uu____6676 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6676 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6684 =
                                           let uu____6685 =
                                             let uu____6692 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6692) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6685 in
                                         (uu____6684,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6713 =
                                             let uu____6714 =
                                               let uu____6715 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6715 in
                                             Prims.strcat module_name
                                               uu____6714 in
                                           varops.mk_unique uu____6713 in
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
                                           let uu____6729 =
                                             let uu____6736 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6736) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6729 in
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
                                           let uu____6751 =
                                             let uu____6758 =
                                               let uu____6759 =
                                                 let uu____6770 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6770) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6759 in
                                             (uu____6758,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6751 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____6796 =
                                             let uu____6803 =
                                               let uu____6804 =
                                                 let uu____6815 =
                                                   let uu____6816 =
                                                     let uu____6821 =
                                                       let uu____6822 =
                                                         let uu____6833 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____6833) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____6822 in
                                                     (uu____6821, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____6816 in
                                                 ([[valid_t]], cvars1,
                                                   uu____6815) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6804 in
                                             (uu____6803,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6796 in
                                         let t_kinding =
                                           let uu____6871 =
                                             let uu____6878 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6878,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6871 in
                                         let t_interp =
                                           let uu____6896 =
                                             let uu____6903 =
                                               let uu____6904 =
                                                 let uu____6915 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6915) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6904 in
                                             let uu____6938 =
                                               let uu____6941 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6941 in
                                             (uu____6903, uu____6938,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6896 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____6948 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6948);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6978 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6978 in
           let uu____6979 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____6979 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6991 =
                    let uu____6998 =
                      let uu____6999 =
                        let uu____7000 =
                          let uu____7001 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7001 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7000 in
                      varops.mk_unique uu____6999 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6998) in
                  FStar_SMTEncoding_Util.mkAssume uu____6991 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7006 ->
           let uu____7021 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7021 with
            | (head1,args_e) ->
                let uu____7062 =
                  let uu____7075 =
                    let uu____7076 = FStar_Syntax_Subst.compress head1 in
                    uu____7076.FStar_Syntax_Syntax.n in
                  (uu____7075, args_e) in
                (match uu____7062 with
                 | uu____7091 when head_redex env head1 ->
                     let uu____7104 = whnf env t in
                     encode_term uu____7104 env
                 | uu____7105 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7124 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7138;
                       FStar_Syntax_Syntax.vars = uu____7139;_},uu____7140),uu____7141::
                    (v1,uu____7143)::(v2,uu____7145)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7196 = encode_term v1 env in
                     (match uu____7196 with
                      | (v11,decls1) ->
                          let uu____7207 = encode_term v2 env in
                          (match uu____7207 with
                           | (v21,decls2) ->
                               let uu____7218 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7218,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7222::(v1,uu____7224)::(v2,uu____7226)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7273 = encode_term v1 env in
                     (match uu____7273 with
                      | (v11,decls1) ->
                          let uu____7284 = encode_term v2 env in
                          (match uu____7284 with
                           | (v21,decls2) ->
                               let uu____7295 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7295,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7298) ->
                     let e0 =
                       let uu____7316 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7316 in
                     ((let uu____7324 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7324
                       then
                         let uu____7325 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7325
                       else ());
                      (let e =
                         let uu____7330 =
                           let uu____7331 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7332 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7331
                             uu____7332 in
                         uu____7330 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7341),(arg,uu____7343)::[]) -> encode_term arg env
                 | uu____7368 ->
                     let uu____7381 = encode_args args_e env in
                     (match uu____7381 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7436 = encode_term head1 env in
                            match uu____7436 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7500 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7500 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7578  ->
                                                 fun uu____7579  ->
                                                   match (uu____7578,
                                                           uu____7579)
                                                   with
                                                   | ((bv,uu____7601),
                                                      (a,uu____7603)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7621 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7621
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7626 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7626 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7641 =
                                                   let uu____7648 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7657 =
                                                     let uu____7658 =
                                                       let uu____7659 =
                                                         let uu____7660 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7660 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7659 in
                                                     varops.mk_unique
                                                       uu____7658 in
                                                   (uu____7648,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7657) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7641 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7677 = lookup_free_var_sym env fv in
                            match uu____7677 with
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
                                   FStar_Syntax_Syntax.pos = uu____7708;
                                   FStar_Syntax_Syntax.vars = uu____7709;_},uu____7710)
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
                                   FStar_Syntax_Syntax.pos = uu____7721;
                                   FStar_Syntax_Syntax.vars = uu____7722;_},uu____7723)
                                ->
                                let uu____7728 =
                                  let uu____7729 =
                                    let uu____7734 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7734
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7729
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7728
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7764 =
                                  let uu____7765 =
                                    let uu____7770 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7770
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7765
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7764
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7799,(FStar_Util.Inl t1,uu____7801),uu____7802)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7851,(FStar_Util.Inr c,uu____7853),uu____7854)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7903 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7930 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7930 in
                               let uu____7931 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____7931 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7947;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7948;_},uu____7949)
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
                                     | uu____7963 ->
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
           let uu____8012 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8012 with
            | (bs1,body1,opening) ->
                let fallback uu____8035 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8042 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8042, [decl]) in
                let is_impure rc =
                  let uu____8049 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8049 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8059 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8059
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8079 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8079
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8083 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8083)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8090 =
                         let uu____8091 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8091 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8090);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8093 =
                       (is_impure rc) &&
                         (let uu____8095 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8095) in
                     if uu____8093
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8102 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8102 with
                        | (vars,guards,envbody,decls,uu____8127) ->
                            let body2 =
                              let uu____8141 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8141
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8143 = encode_term body2 envbody in
                            (match uu____8143 with
                             | (body3,decls') ->
                                 let uu____8154 =
                                   let uu____8163 = codomain_eff rc in
                                   match uu____8163 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8182 = encode_term tfun env in
                                       (match uu____8182 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8154 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8214 =
                                          let uu____8225 =
                                            let uu____8226 =
                                              let uu____8231 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8231, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8226 in
                                          ([], vars, uu____8225) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8214 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8243 =
                                              let uu____8246 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8246
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8243 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8265 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8265 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8273 =
                                             let uu____8274 =
                                               let uu____8281 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8281) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8274 in
                                           (uu____8273,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8292 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8292 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8303 =
                                                    let uu____8304 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8304 = cache_size in
                                                  if uu____8303
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
                                                    let uu____8320 =
                                                      let uu____8321 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8321 in
                                                    varops.mk_unique
                                                      uu____8320 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8328 =
                                                    let uu____8335 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8335) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8328 in
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
                                                      let uu____8353 =
                                                        let uu____8354 =
                                                          let uu____8361 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8361,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8354 in
                                                      [uu____8353] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8374 =
                                                    let uu____8381 =
                                                      let uu____8382 =
                                                        let uu____8393 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8393) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8382 in
                                                    (uu____8381,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8374 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8410 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8410);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8413,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8414;
                          FStar_Syntax_Syntax.lbunivs = uu____8415;
                          FStar_Syntax_Syntax.lbtyp = uu____8416;
                          FStar_Syntax_Syntax.lbeff = uu____8417;
                          FStar_Syntax_Syntax.lbdef = uu____8418;_}::uu____8419),uu____8420)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8446;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8448;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8469 ->
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
              let uu____8539 = encode_term e1 env in
              match uu____8539 with
              | (ee1,decls1) ->
                  let uu____8550 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8550 with
                   | (xs,e21) ->
                       let uu____8575 = FStar_List.hd xs in
                       (match uu____8575 with
                        | (x1,uu____8589) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8591 = encode_body e21 env' in
                            (match uu____8591 with
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
            let uu____8623 =
              let uu____8630 =
                let uu____8631 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8631 in
              gen_term_var env uu____8630 in
            match uu____8623 with
            | (scrsym,scr',env1) ->
                let uu____8639 = encode_term e env1 in
                (match uu____8639 with
                 | (scr,decls) ->
                     let uu____8650 =
                       let encode_branch b uu____8675 =
                         match uu____8675 with
                         | (else_case,decls1) ->
                             let uu____8694 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8694 with
                              | (p,w,br) ->
                                  let uu____8720 = encode_pat env1 p in
                                  (match uu____8720 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8757  ->
                                                   match uu____8757 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8764 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8786 =
                                               encode_term w1 env2 in
                                             (match uu____8786 with
                                              | (w2,decls2) ->
                                                  let uu____8799 =
                                                    let uu____8800 =
                                                      let uu____8805 =
                                                        let uu____8806 =
                                                          let uu____8811 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8811) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8806 in
                                                      (guard, uu____8805) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8800 in
                                                  (uu____8799, decls2)) in
                                       (match uu____8764 with
                                        | (guard1,decls2) ->
                                            let uu____8824 =
                                              encode_br br env2 in
                                            (match uu____8824 with
                                             | (br1,decls3) ->
                                                 let uu____8837 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8837,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8650 with
                      | (match_tm,decls1) ->
                          let uu____8856 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____8856, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____8896 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____8896
       then
         let uu____8897 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8897
       else ());
      (let uu____8899 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____8899 with
       | (vars,pat_term) ->
           let uu____8916 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8969  ->
                     fun v1  ->
                       match uu____8969 with
                       | (env1,vars1) ->
                           let uu____9021 = gen_term_var env1 v1 in
                           (match uu____9021 with
                            | (xx,uu____9043,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____8916 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9122 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9123 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9124 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9132 =
                        let uu____9137 = encode_const c in
                        (scrutinee, uu____9137) in
                      FStar_SMTEncoding_Util.mkEq uu____9132
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9158 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9158 with
                        | (uu____9165,uu____9166::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9169 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9202  ->
                                  match uu____9202 with
                                  | (arg,uu____9210) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9216 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9216)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9243) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9274 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9297 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9341  ->
                                  match uu____9341 with
                                  | (arg,uu____9355) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9361 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9361)) in
                      FStar_All.pipe_right uu____9297 FStar_List.flatten in
                let pat_term1 uu____9389 = encode_term pat_term env1 in
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
      let uu____9399 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9437  ->
                fun uu____9438  ->
                  match (uu____9437, uu____9438) with
                  | ((tms,decls),(t,uu____9474)) ->
                      let uu____9495 = encode_term t env in
                      (match uu____9495 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9399 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9552 = FStar_Syntax_Util.list_elements e in
        match uu____9552 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9573 =
          let uu____9588 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9588 FStar_Syntax_Util.head_and_args in
        match uu____9573 with
        | (head1,args) ->
            let uu____9627 =
              let uu____9640 =
                let uu____9641 = FStar_Syntax_Util.un_uinst head1 in
                uu____9641.FStar_Syntax_Syntax.n in
              (uu____9640, args) in
            (match uu____9627 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9655,uu____9656)::(e,uu____9658)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9693 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9729 =
            let uu____9744 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9744 FStar_Syntax_Util.head_and_args in
          match uu____9729 with
          | (head1,args) ->
              let uu____9785 =
                let uu____9798 =
                  let uu____9799 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9799.FStar_Syntax_Syntax.n in
                (uu____9798, args) in
              (match uu____9785 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9816)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9843 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____9865 = smt_pat_or1 t1 in
            (match uu____9865 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9881 = list_elements1 e in
                 FStar_All.pipe_right uu____9881
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9899 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____9899
                           (FStar_List.map one_pat)))
             | uu____9910 ->
                 let uu____9915 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____9915])
        | uu____9936 ->
            let uu____9939 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____9939] in
      let uu____9960 =
        let uu____9979 =
          let uu____9980 = FStar_Syntax_Subst.compress t in
          uu____9980.FStar_Syntax_Syntax.n in
        match uu____9979 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10019 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10019 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10062;
                        FStar_Syntax_Syntax.effect_name = uu____10063;
                        FStar_Syntax_Syntax.result_typ = uu____10064;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10066)::(post,uu____10068)::(pats,uu____10070)::[];
                        FStar_Syntax_Syntax.flags = uu____10071;_}
                      ->
                      let uu____10112 = lemma_pats pats in
                      (binders1, pre, post, uu____10112)
                  | uu____10129 -> failwith "impos"))
        | uu____10148 -> failwith "Impos" in
      match uu____9960 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___142_10196 = env in
            {
              bindings = (uu___142_10196.bindings);
              depth = (uu___142_10196.depth);
              tcenv = (uu___142_10196.tcenv);
              warn = (uu___142_10196.warn);
              cache = (uu___142_10196.cache);
              nolabels = (uu___142_10196.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___142_10196.encode_non_total_function_typ);
              current_module_name = (uu___142_10196.current_module_name)
            } in
          let uu____10197 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10197 with
           | (vars,guards,env2,decls,uu____10222) ->
               let uu____10235 =
                 let uu____10248 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10292 =
                             let uu____10301 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10301
                               FStar_List.unzip in
                           match uu____10292 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10248 FStar_List.unzip in
               (match uu____10235 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___143_10410 = env2 in
                      {
                        bindings = (uu___143_10410.bindings);
                        depth = (uu___143_10410.depth);
                        tcenv = (uu___143_10410.tcenv);
                        warn = (uu___143_10410.warn);
                        cache = (uu___143_10410.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___143_10410.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___143_10410.encode_non_total_function_typ);
                        current_module_name =
                          (uu___143_10410.current_module_name)
                      } in
                    let uu____10411 =
                      let uu____10416 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10416 env3 in
                    (match uu____10411 with
                     | (pre1,decls'') ->
                         let uu____10423 =
                           let uu____10428 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10428 env3 in
                         (match uu____10423 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10438 =
                                let uu____10439 =
                                  let uu____10450 =
                                    let uu____10451 =
                                      let uu____10456 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10456, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____10451 in
                                  (pats, vars, uu____10450) in
                                FStar_SMTEncoding_Util.mkForall uu____10439 in
                              (uu____10438, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10475 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10475
        then
          let uu____10476 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10477 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10476 uu____10477
        else () in
      let enc f r l =
        let uu____10510 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10538 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10538 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10510 with
        | (decls,args) ->
            let uu____10567 =
              let uu___144_10568 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_10568.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_10568.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10567, decls) in
      let const_op f r uu____10599 =
        let uu____10612 = f r in (uu____10612, []) in
      let un_op f l =
        let uu____10631 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10631 in
      let bin_op f uu___118_10647 =
        match uu___118_10647 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10658 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10692 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10715  ->
                 match uu____10715 with
                 | (t,uu____10729) ->
                     let uu____10730 = encode_formula t env in
                     (match uu____10730 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10692 with
        | (decls,phis) ->
            let uu____10759 =
              let uu___145_10760 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___145_10760.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___145_10760.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10759, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10821  ->
               match uu____10821 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____10840) -> false
                    | uu____10841 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____10856 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____10856
        else
          (let uu____10870 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____10870 r rf) in
      let mk_imp1 r uu___119_10895 =
        match uu___119_10895 with
        | (lhs,uu____10901)::(rhs,uu____10903)::[] ->
            let uu____10930 = encode_formula rhs env in
            (match uu____10930 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____10945) ->
                      (l1, decls1)
                  | uu____10950 ->
                      let uu____10951 = encode_formula lhs env in
                      (match uu____10951 with
                       | (l2,decls2) ->
                           let uu____10962 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____10962, (FStar_List.append decls1 decls2)))))
        | uu____10965 -> failwith "impossible" in
      let mk_ite r uu___120_10986 =
        match uu___120_10986 with
        | (guard,uu____10992)::(_then,uu____10994)::(_else,uu____10996)::[]
            ->
            let uu____11033 = encode_formula guard env in
            (match uu____11033 with
             | (g,decls1) ->
                 let uu____11044 = encode_formula _then env in
                 (match uu____11044 with
                  | (t,decls2) ->
                      let uu____11055 = encode_formula _else env in
                      (match uu____11055 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11069 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11094 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11094 in
      let connectives =
        let uu____11112 =
          let uu____11125 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11125) in
        let uu____11142 =
          let uu____11157 =
            let uu____11170 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11170) in
          let uu____11187 =
            let uu____11202 =
              let uu____11217 =
                let uu____11230 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11230) in
              let uu____11247 =
                let uu____11262 =
                  let uu____11277 =
                    let uu____11290 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11290) in
                  [uu____11277;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11262 in
              uu____11217 :: uu____11247 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11202 in
          uu____11157 :: uu____11187 in
        uu____11112 :: uu____11142 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11611 = encode_formula phi' env in
            (match uu____11611 with
             | (phi2,decls) ->
                 let uu____11622 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11622, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11623 ->
            let uu____11630 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11630 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11669 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11669 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11681;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11683;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11704 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11704 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11751::(x,uu____11753)::(t,uu____11755)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11802 = encode_term x env in
                 (match uu____11802 with
                  | (x1,decls) ->
                      let uu____11813 = encode_term t env in
                      (match uu____11813 with
                       | (t1,decls') ->
                           let uu____11824 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11824, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11829)::(msg,uu____11831)::(phi2,uu____11833)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____11878 =
                   let uu____11883 =
                     let uu____11884 = FStar_Syntax_Subst.compress r in
                     uu____11884.FStar_Syntax_Syntax.n in
                   let uu____11887 =
                     let uu____11888 = FStar_Syntax_Subst.compress msg in
                     uu____11888.FStar_Syntax_Syntax.n in
                   (uu____11883, uu____11887) in
                 (match uu____11878 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____11897))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____11903 -> fallback phi2)
             | uu____11908 when head_redex env head2 ->
                 let uu____11921 = whnf env phi1 in
                 encode_formula uu____11921 env
             | uu____11922 ->
                 let uu____11935 = encode_term phi1 env in
                 (match uu____11935 with
                  | (tt,decls) ->
                      let uu____11946 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___146_11949 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___146_11949.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___146_11949.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____11946, decls)))
        | uu____11950 ->
            let uu____11951 = encode_term phi1 env in
            (match uu____11951 with
             | (tt,decls) ->
                 let uu____11962 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___147_11965 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___147_11965.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___147_11965.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____11962, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12001 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12001 with
        | (vars,guards,env2,decls,uu____12040) ->
            let uu____12053 =
              let uu____12066 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12114 =
                          let uu____12123 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12153  ->
                                    match uu____12153 with
                                    | (t,uu____12163) ->
                                        encode_term t
                                          (let uu___148_12165 = env2 in
                                           {
                                             bindings =
                                               (uu___148_12165.bindings);
                                             depth = (uu___148_12165.depth);
                                             tcenv = (uu___148_12165.tcenv);
                                             warn = (uu___148_12165.warn);
                                             cache = (uu___148_12165.cache);
                                             nolabels =
                                               (uu___148_12165.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___148_12165.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___148_12165.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12123 FStar_List.unzip in
                        match uu____12114 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12066 FStar_List.unzip in
            (match uu____12053 with
             | (pats,decls') ->
                 let uu____12264 = encode_formula body env2 in
                 (match uu____12264 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12296;
                             FStar_SMTEncoding_Term.rng = uu____12297;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12312 -> guards in
                      let uu____12317 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12317, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12377  ->
                   match uu____12377 with
                   | (x,uu____12383) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12391 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12403 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12403) uu____12391 tl1 in
             let uu____12406 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12433  ->
                       match uu____12433 with
                       | (b,uu____12439) ->
                           let uu____12440 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12440)) in
             (match uu____12406 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12446) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12460 =
                    let uu____12461 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12461 in
                  FStar_Errors.warn pos uu____12460) in
       let uu____12462 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12462 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12471 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12529  ->
                     match uu____12529 with
                     | (l,uu____12543) -> FStar_Ident.lid_equals op l)) in
           (match uu____12471 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12576,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12616 = encode_q_body env vars pats body in
             match uu____12616 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12661 =
                     let uu____12672 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12672) in
                   FStar_SMTEncoding_Term.mkForall uu____12661
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12691 = encode_q_body env vars pats body in
             match uu____12691 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12735 =
                   let uu____12736 =
                     let uu____12747 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12747) in
                   FStar_SMTEncoding_Term.mkExists uu____12736
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12735, decls))))
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
  let uu____12845 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____12845 with
  | (asym,a) ->
      let uu____12852 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____12852 with
       | (xsym,x) ->
           let uu____12859 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____12859 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____12903 =
                      let uu____12914 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____12914, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____12903 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____12940 =
                      let uu____12947 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____12947) in
                    FStar_SMTEncoding_Util.mkApp uu____12940 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____12960 =
                    let uu____12963 =
                      let uu____12966 =
                        let uu____12969 =
                          let uu____12970 =
                            let uu____12977 =
                              let uu____12978 =
                                let uu____12989 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____12989) in
                              FStar_SMTEncoding_Util.mkForall uu____12978 in
                            (uu____12977, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____12970 in
                        let uu____13006 =
                          let uu____13009 =
                            let uu____13010 =
                              let uu____13017 =
                                let uu____13018 =
                                  let uu____13029 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13029) in
                                FStar_SMTEncoding_Util.mkForall uu____13018 in
                              (uu____13017,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13010 in
                          [uu____13009] in
                        uu____12969 :: uu____13006 in
                      xtok_decl :: uu____12966 in
                    xname_decl :: uu____12963 in
                  (xtok1, uu____12960) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13120 =
                    let uu____13133 =
                      let uu____13142 =
                        let uu____13143 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13143 in
                      quant axy uu____13142 in
                    (FStar_Parser_Const.op_Eq, uu____13133) in
                  let uu____13152 =
                    let uu____13167 =
                      let uu____13180 =
                        let uu____13189 =
                          let uu____13190 =
                            let uu____13191 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13191 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13190 in
                        quant axy uu____13189 in
                      (FStar_Parser_Const.op_notEq, uu____13180) in
                    let uu____13200 =
                      let uu____13215 =
                        let uu____13228 =
                          let uu____13237 =
                            let uu____13238 =
                              let uu____13239 =
                                let uu____13244 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13245 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13244, uu____13245) in
                              FStar_SMTEncoding_Util.mkLT uu____13239 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13238 in
                          quant xy uu____13237 in
                        (FStar_Parser_Const.op_LT, uu____13228) in
                      let uu____13254 =
                        let uu____13269 =
                          let uu____13282 =
                            let uu____13291 =
                              let uu____13292 =
                                let uu____13293 =
                                  let uu____13298 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13299 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13298, uu____13299) in
                                FStar_SMTEncoding_Util.mkLTE uu____13293 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13292 in
                            quant xy uu____13291 in
                          (FStar_Parser_Const.op_LTE, uu____13282) in
                        let uu____13308 =
                          let uu____13323 =
                            let uu____13336 =
                              let uu____13345 =
                                let uu____13346 =
                                  let uu____13347 =
                                    let uu____13352 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13353 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13352, uu____13353) in
                                  FStar_SMTEncoding_Util.mkGT uu____13347 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13346 in
                              quant xy uu____13345 in
                            (FStar_Parser_Const.op_GT, uu____13336) in
                          let uu____13362 =
                            let uu____13377 =
                              let uu____13390 =
                                let uu____13399 =
                                  let uu____13400 =
                                    let uu____13401 =
                                      let uu____13406 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13407 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13406, uu____13407) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13401 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13400 in
                                quant xy uu____13399 in
                              (FStar_Parser_Const.op_GTE, uu____13390) in
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
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13455 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13454 in
                                  quant xy uu____13453 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13444) in
                              let uu____13470 =
                                let uu____13485 =
                                  let uu____13498 =
                                    let uu____13507 =
                                      let uu____13508 =
                                        let uu____13509 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13509 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13508 in
                                    quant qx uu____13507 in
                                  (FStar_Parser_Const.op_Minus, uu____13498) in
                                let uu____13518 =
                                  let uu____13533 =
                                    let uu____13546 =
                                      let uu____13555 =
                                        let uu____13556 =
                                          let uu____13557 =
                                            let uu____13562 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13563 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13562, uu____13563) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13557 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13556 in
                                      quant xy uu____13555 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13546) in
                                  let uu____13572 =
                                    let uu____13587 =
                                      let uu____13600 =
                                        let uu____13609 =
                                          let uu____13610 =
                                            let uu____13611 =
                                              let uu____13616 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13617 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13616, uu____13617) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13611 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13610 in
                                        quant xy uu____13609 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13600) in
                                    let uu____13626 =
                                      let uu____13641 =
                                        let uu____13654 =
                                          let uu____13663 =
                                            let uu____13664 =
                                              let uu____13665 =
                                                let uu____13670 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13671 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13670, uu____13671) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13665 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13664 in
                                          quant xy uu____13663 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13654) in
                                      let uu____13680 =
                                        let uu____13695 =
                                          let uu____13708 =
                                            let uu____13717 =
                                              let uu____13718 =
                                                let uu____13719 =
                                                  let uu____13724 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13725 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13724, uu____13725) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13719 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13718 in
                                            quant xy uu____13717 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13708) in
                                        let uu____13734 =
                                          let uu____13749 =
                                            let uu____13762 =
                                              let uu____13771 =
                                                let uu____13772 =
                                                  let uu____13773 =
                                                    let uu____13778 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13779 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13778,
                                                      uu____13779) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13773 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13772 in
                                              quant xy uu____13771 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13762) in
                                          let uu____13788 =
                                            let uu____13803 =
                                              let uu____13816 =
                                                let uu____13825 =
                                                  let uu____13826 =
                                                    let uu____13827 =
                                                      let uu____13832 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____13833 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____13832,
                                                        uu____13833) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13827 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13826 in
                                                quant xy uu____13825 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13816) in
                                            let uu____13842 =
                                              let uu____13857 =
                                                let uu____13870 =
                                                  let uu____13879 =
                                                    let uu____13880 =
                                                      let uu____13881 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____13881 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____13880 in
                                                  quant qx uu____13879 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____13870) in
                                              [uu____13857] in
                                            uu____13803 :: uu____13842 in
                                          uu____13749 :: uu____13788 in
                                        uu____13695 :: uu____13734 in
                                      uu____13641 :: uu____13680 in
                                    uu____13587 :: uu____13626 in
                                  uu____13533 :: uu____13572 in
                                uu____13485 :: uu____13518 in
                              uu____13431 :: uu____13470 in
                            uu____13377 :: uu____13416 in
                          uu____13323 :: uu____13362 in
                        uu____13269 :: uu____13308 in
                      uu____13215 :: uu____13254 in
                    uu____13167 :: uu____13200 in
                  uu____13120 :: uu____13152 in
                let mk1 l v1 =
                  let uu____14095 =
                    let uu____14104 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14162  ->
                              match uu____14162 with
                              | (l',uu____14176) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14104
                      (FStar_Option.map
                         (fun uu____14236  ->
                            match uu____14236 with | (uu____14255,b) -> b v1)) in
                  FStar_All.pipe_right uu____14095 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14326  ->
                          match uu____14326 with
                          | (l',uu____14340) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14381 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14381 with
        | (xxsym,xx) ->
            let uu____14388 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14388 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14398 =
                   let uu____14405 =
                     let uu____14406 =
                       let uu____14417 =
                         let uu____14418 =
                           let uu____14423 =
                             let uu____14424 =
                               let uu____14429 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14429) in
                             FStar_SMTEncoding_Util.mkEq uu____14424 in
                           (xx_has_type, uu____14423) in
                         FStar_SMTEncoding_Util.mkImp uu____14418 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14417) in
                     FStar_SMTEncoding_Util.mkForall uu____14406 in
                   let uu____14454 =
                     let uu____14455 =
                       let uu____14456 =
                         let uu____14457 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14457 in
                       Prims.strcat module_name uu____14456 in
                     varops.mk_unique uu____14455 in
                   (uu____14405, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14454) in
                 FStar_SMTEncoding_Util.mkAssume uu____14398)
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
    let uu____14497 =
      let uu____14498 =
        let uu____14505 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14505, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14498 in
    let uu____14508 =
      let uu____14511 =
        let uu____14512 =
          let uu____14519 =
            let uu____14520 =
              let uu____14531 =
                let uu____14532 =
                  let uu____14537 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14537) in
                FStar_SMTEncoding_Util.mkImp uu____14532 in
              ([[typing_pred]], [xx], uu____14531) in
            mkForall_fuel uu____14520 in
          (uu____14519, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14512 in
      [uu____14511] in
    uu____14497 :: uu____14508 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14579 =
      let uu____14580 =
        let uu____14587 =
          let uu____14588 =
            let uu____14599 =
              let uu____14604 =
                let uu____14607 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14607] in
              [uu____14604] in
            let uu____14612 =
              let uu____14613 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14613 tt in
            (uu____14599, [bb], uu____14612) in
          FStar_SMTEncoding_Util.mkForall uu____14588 in
        (uu____14587, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14580 in
    let uu____14634 =
      let uu____14637 =
        let uu____14638 =
          let uu____14645 =
            let uu____14646 =
              let uu____14657 =
                let uu____14658 =
                  let uu____14663 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14663) in
                FStar_SMTEncoding_Util.mkImp uu____14658 in
              ([[typing_pred]], [xx], uu____14657) in
            mkForall_fuel uu____14646 in
          (uu____14645, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14638 in
      [uu____14637] in
    uu____14579 :: uu____14634 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14713 =
        let uu____14714 =
          let uu____14721 =
            let uu____14724 =
              let uu____14727 =
                let uu____14730 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14731 =
                  let uu____14734 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14734] in
                uu____14730 :: uu____14731 in
              tt :: uu____14727 in
            tt :: uu____14724 in
          ("Prims.Precedes", uu____14721) in
        FStar_SMTEncoding_Util.mkApp uu____14714 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14713 in
    let precedes_y_x =
      let uu____14738 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14738 in
    let uu____14741 =
      let uu____14742 =
        let uu____14749 =
          let uu____14750 =
            let uu____14761 =
              let uu____14766 =
                let uu____14769 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14769] in
              [uu____14766] in
            let uu____14774 =
              let uu____14775 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14775 tt in
            (uu____14761, [bb], uu____14774) in
          FStar_SMTEncoding_Util.mkForall uu____14750 in
        (uu____14749, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14742 in
    let uu____14796 =
      let uu____14799 =
        let uu____14800 =
          let uu____14807 =
            let uu____14808 =
              let uu____14819 =
                let uu____14820 =
                  let uu____14825 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14825) in
                FStar_SMTEncoding_Util.mkImp uu____14820 in
              ([[typing_pred]], [xx], uu____14819) in
            mkForall_fuel uu____14808 in
          (uu____14807, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14800 in
      let uu____14850 =
        let uu____14853 =
          let uu____14854 =
            let uu____14861 =
              let uu____14862 =
                let uu____14873 =
                  let uu____14874 =
                    let uu____14879 =
                      let uu____14880 =
                        let uu____14883 =
                          let uu____14886 =
                            let uu____14889 =
                              let uu____14890 =
                                let uu____14895 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____14896 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____14895, uu____14896) in
                              FStar_SMTEncoding_Util.mkGT uu____14890 in
                            let uu____14897 =
                              let uu____14900 =
                                let uu____14901 =
                                  let uu____14906 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____14907 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____14906, uu____14907) in
                                FStar_SMTEncoding_Util.mkGTE uu____14901 in
                              let uu____14908 =
                                let uu____14911 =
                                  let uu____14912 =
                                    let uu____14917 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____14918 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____14917, uu____14918) in
                                  FStar_SMTEncoding_Util.mkLT uu____14912 in
                                [uu____14911] in
                              uu____14900 :: uu____14908 in
                            uu____14889 :: uu____14897 in
                          typing_pred_y :: uu____14886 in
                        typing_pred :: uu____14883 in
                      FStar_SMTEncoding_Util.mk_and_l uu____14880 in
                    (uu____14879, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____14874 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____14873) in
              mkForall_fuel uu____14862 in
            (uu____14861,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____14854 in
        [uu____14853] in
      uu____14799 :: uu____14850 in
    uu____14741 :: uu____14796 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14964 =
      let uu____14965 =
        let uu____14972 =
          let uu____14973 =
            let uu____14984 =
              let uu____14989 =
                let uu____14992 = FStar_SMTEncoding_Term.boxString b in
                [uu____14992] in
              [uu____14989] in
            let uu____14997 =
              let uu____14998 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____14998 tt in
            (uu____14984, [bb], uu____14997) in
          FStar_SMTEncoding_Util.mkForall uu____14973 in
        (uu____14972, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14965 in
    let uu____15019 =
      let uu____15022 =
        let uu____15023 =
          let uu____15030 =
            let uu____15031 =
              let uu____15042 =
                let uu____15043 =
                  let uu____15048 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15048) in
                FStar_SMTEncoding_Util.mkImp uu____15043 in
              ([[typing_pred]], [xx], uu____15042) in
            mkForall_fuel uu____15031 in
          (uu____15030, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15023 in
      [uu____15022] in
    uu____14964 :: uu____15019 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15101 =
      let uu____15102 =
        let uu____15109 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15109, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15102 in
    [uu____15101] in
  let mk_and_interp env conj uu____15121 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15146 =
      let uu____15147 =
        let uu____15154 =
          let uu____15155 =
            let uu____15166 =
              let uu____15167 =
                let uu____15172 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15172, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15167 in
            ([[l_and_a_b]], [aa; bb], uu____15166) in
          FStar_SMTEncoding_Util.mkForall uu____15155 in
        (uu____15154, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15147 in
    [uu____15146] in
  let mk_or_interp env disj uu____15210 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15235 =
      let uu____15236 =
        let uu____15243 =
          let uu____15244 =
            let uu____15255 =
              let uu____15256 =
                let uu____15261 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15261, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15256 in
            ([[l_or_a_b]], [aa; bb], uu____15255) in
          FStar_SMTEncoding_Util.mkForall uu____15244 in
        (uu____15243, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15236 in
    [uu____15235] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15324 =
      let uu____15325 =
        let uu____15332 =
          let uu____15333 =
            let uu____15344 =
              let uu____15345 =
                let uu____15350 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15350, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15345 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15344) in
          FStar_SMTEncoding_Util.mkForall uu____15333 in
        (uu____15332, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15325 in
    [uu____15324] in
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
    let uu____15423 =
      let uu____15424 =
        let uu____15431 =
          let uu____15432 =
            let uu____15443 =
              let uu____15444 =
                let uu____15449 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15449, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15444 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15443) in
          FStar_SMTEncoding_Util.mkForall uu____15432 in
        (uu____15431, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15424 in
    [uu____15423] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15520 =
      let uu____15521 =
        let uu____15528 =
          let uu____15529 =
            let uu____15540 =
              let uu____15541 =
                let uu____15546 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15546, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15541 in
            ([[l_imp_a_b]], [aa; bb], uu____15540) in
          FStar_SMTEncoding_Util.mkForall uu____15529 in
        (uu____15528, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15521 in
    [uu____15520] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15609 =
      let uu____15610 =
        let uu____15617 =
          let uu____15618 =
            let uu____15629 =
              let uu____15630 =
                let uu____15635 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15635, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15630 in
            ([[l_iff_a_b]], [aa; bb], uu____15629) in
          FStar_SMTEncoding_Util.mkForall uu____15618 in
        (uu____15617, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15610 in
    [uu____15609] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15687 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15687 in
    let uu____15690 =
      let uu____15691 =
        let uu____15698 =
          let uu____15699 =
            let uu____15710 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15710) in
          FStar_SMTEncoding_Util.mkForall uu____15699 in
        (uu____15698, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15691 in
    [uu____15690] in
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
      let uu____15770 =
        let uu____15777 =
          let uu____15780 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15780] in
        ("Valid", uu____15777) in
      FStar_SMTEncoding_Util.mkApp uu____15770 in
    let uu____15783 =
      let uu____15784 =
        let uu____15791 =
          let uu____15792 =
            let uu____15803 =
              let uu____15804 =
                let uu____15809 =
                  let uu____15810 =
                    let uu____15821 =
                      let uu____15826 =
                        let uu____15829 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15829] in
                      [uu____15826] in
                    let uu____15834 =
                      let uu____15835 =
                        let uu____15840 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15840, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15835 in
                    (uu____15821, [xx1], uu____15834) in
                  FStar_SMTEncoding_Util.mkForall uu____15810 in
                (uu____15809, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15804 in
            ([[l_forall_a_b]], [aa; bb], uu____15803) in
          FStar_SMTEncoding_Util.mkForall uu____15792 in
        (uu____15791, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15784 in
    [uu____15783] in
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
      let uu____15922 =
        let uu____15929 =
          let uu____15932 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15932] in
        ("Valid", uu____15929) in
      FStar_SMTEncoding_Util.mkApp uu____15922 in
    let uu____15935 =
      let uu____15936 =
        let uu____15943 =
          let uu____15944 =
            let uu____15955 =
              let uu____15956 =
                let uu____15961 =
                  let uu____15962 =
                    let uu____15973 =
                      let uu____15978 =
                        let uu____15981 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15981] in
                      [uu____15978] in
                    let uu____15986 =
                      let uu____15987 =
                        let uu____15992 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15992, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15987 in
                    (uu____15973, [xx1], uu____15986) in
                  FStar_SMTEncoding_Util.mkExists uu____15962 in
                (uu____15961, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15956 in
            ([[l_exists_a_b]], [aa; bb], uu____15955) in
          FStar_SMTEncoding_Util.mkForall uu____15944 in
        (uu____15943, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15936 in
    [uu____15935] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16052 =
      let uu____16053 =
        let uu____16060 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16061 = varops.mk_unique "typing_range_const" in
        (uu____16060, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16061) in
      FStar_SMTEncoding_Util.mkAssume uu____16053 in
    [uu____16052] in
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
        let uu____16095 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16095 x1 t in
      let uu____16096 =
        let uu____16107 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16107) in
      FStar_SMTEncoding_Util.mkForall uu____16096 in
    let uu____16130 =
      let uu____16131 =
        let uu____16138 =
          let uu____16139 =
            let uu____16150 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16150) in
          FStar_SMTEncoding_Util.mkForall uu____16139 in
        (uu____16138,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16131 in
    [uu____16130] in
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
          let uu____16474 =
            FStar_Util.find_opt
              (fun uu____16500  ->
                 match uu____16500 with
                 | (l,uu____16512) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16474 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16537,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16576 = encode_function_type_as_formula t env in
        match uu____16576 with
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
              let uu____16622 =
                ((let uu____16625 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16625) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16622
              then
                let uu____16632 = new_term_constant_and_tok_from_lid env lid in
                match uu____16632 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16651 =
                        let uu____16652 = FStar_Syntax_Subst.compress t_norm in
                        uu____16652.FStar_Syntax_Syntax.n in
                      match uu____16651 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16658) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16688  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16693 -> [] in
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
                (let uu____16707 = prims.is lid in
                 if uu____16707
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16715 = prims.mk lid vname in
                   match uu____16715 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16739 =
                      let uu____16750 = curried_arrow_formals_comp t_norm in
                      match uu____16750 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16768 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16768
                            then
                              let uu____16769 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___149_16772 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___149_16772.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___149_16772.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___149_16772.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___149_16772.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___149_16772.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___149_16772.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___149_16772.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___149_16772.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___149_16772.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___149_16772.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___149_16772.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___149_16772.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___149_16772.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___149_16772.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___149_16772.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___149_16772.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___149_16772.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___149_16772.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___149_16772.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___149_16772.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___149_16772.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___149_16772.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___149_16772.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___149_16772.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___149_16772.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___149_16772.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___149_16772.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___149_16772.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___149_16772.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16769
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16784 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16784)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16739 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16829 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16829 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____16850 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___121_16892  ->
                                       match uu___121_16892 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____16896 =
                                             FStar_Util.prefix vars in
                                           (match uu____16896 with
                                            | (uu____16917,(xxsym,uu____16919))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____16937 =
                                                  let uu____16938 =
                                                    let uu____16945 =
                                                      let uu____16946 =
                                                        let uu____16957 =
                                                          let uu____16958 =
                                                            let uu____16963 =
                                                              let uu____16964
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____16964 in
                                                            (vapp,
                                                              uu____16963) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____16958 in
                                                        ([[vapp]], vars,
                                                          uu____16957) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____16946 in
                                                    (uu____16945,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____16938 in
                                                [uu____16937])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____16983 =
                                             FStar_Util.prefix vars in
                                           (match uu____16983 with
                                            | (uu____17004,(xxsym,uu____17006))
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
                                                let uu____17029 =
                                                  let uu____17030 =
                                                    let uu____17037 =
                                                      let uu____17038 =
                                                        let uu____17049 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17049) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17038 in
                                                    (uu____17037,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17030 in
                                                [uu____17029])
                                       | uu____17066 -> [])) in
                             let uu____17067 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17067 with
                              | (vars,guards,env',decls1,uu____17094) ->
                                  let uu____17107 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17116 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17116, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17118 =
                                          encode_formula p env' in
                                        (match uu____17118 with
                                         | (g,ds) ->
                                             let uu____17129 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17129,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17107 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17142 =
                                           let uu____17149 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17149) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17142 in
                                       let uu____17158 =
                                         let vname_decl =
                                           let uu____17166 =
                                             let uu____17177 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17187  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17177,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17166 in
                                         let uu____17196 =
                                           let env2 =
                                             let uu___150_17202 = env1 in
                                             {
                                               bindings =
                                                 (uu___150_17202.bindings);
                                               depth = (uu___150_17202.depth);
                                               tcenv = (uu___150_17202.tcenv);
                                               warn = (uu___150_17202.warn);
                                               cache = (uu___150_17202.cache);
                                               nolabels =
                                                 (uu___150_17202.nolabels);
                                               use_zfuel_name =
                                                 (uu___150_17202.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___150_17202.current_module_name)
                                             } in
                                           let uu____17203 =
                                             let uu____17204 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17204 in
                                           if uu____17203
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17196 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17219::uu____17220 ->
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
                                                     let uu____17260 =
                                                       let uu____17271 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17271) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17260 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17298 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17301 =
                                               match formals with
                                               | [] ->
                                                   let uu____17318 =
                                                     let uu____17319 =
                                                       let uu____17322 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17322 in
                                                     push_free_var env1 lid
                                                       vname uu____17319 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17318)
                                               | uu____17327 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let vtok_fresh =
                                                     let uu____17334 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17334 in
                                                   let name_tok_corr =
                                                     let uu____17336 =
                                                       let uu____17343 =
                                                         let uu____17344 =
                                                           let uu____17355 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17355) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17344 in
                                                       (uu____17343,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17336 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17301 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17158 with
                                        | (decls2,env2) ->
                                            let uu____17398 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17406 =
                                                encode_term res_t1 env' in
                                              match uu____17406 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17419 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17419, decls) in
                                            (match uu____17398 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17430 =
                                                     let uu____17437 =
                                                       let uu____17438 =
                                                         let uu____17449 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17449) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17438 in
                                                     (uu____17437,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17430 in
                                                 let freshness =
                                                   let uu____17465 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17465
                                                   then
                                                     let uu____17470 =
                                                       let uu____17471 =
                                                         let uu____17482 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17493 =
                                                           varops.next_id () in
                                                         (vname, uu____17482,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17493) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17471 in
                                                     let uu____17496 =
                                                       let uu____17499 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17499] in
                                                     uu____17470 ::
                                                       uu____17496
                                                   else [] in
                                                 let g =
                                                   let uu____17504 =
                                                     let uu____17507 =
                                                       let uu____17510 =
                                                         let uu____17513 =
                                                           let uu____17516 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17516 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17513 in
                                                       FStar_List.append
                                                         decls3 uu____17510 in
                                                     FStar_List.append decls2
                                                       uu____17507 in
                                                   FStar_List.append decls11
                                                     uu____17504 in
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
          let uu____17551 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17551 with
          | FStar_Pervasives_Native.None  ->
              let uu____17588 = encode_free_var false env x t t_norm [] in
              (match uu____17588 with
               | (decls,env1) ->
                   let uu____17615 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17615 with
                    | (n1,x',uu____17642) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17663) ->
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
            let uu____17723 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17723 with
            | (decls,env1) ->
                let uu____17742 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17742
                then
                  let uu____17749 =
                    let uu____17752 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17752 in
                  (uu____17749, env1)
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
             (fun uu____17807  ->
                fun lb  ->
                  match uu____17807 with
                  | (decls,env1) ->
                      let uu____17827 =
                        let uu____17834 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17834
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17827 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____17856 = FStar_Syntax_Util.head_and_args t in
    match uu____17856 with
    | (hd1,args) ->
        let uu____17893 =
          let uu____17894 = FStar_Syntax_Util.un_uinst hd1 in
          uu____17894.FStar_Syntax_Syntax.n in
        (match uu____17893 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____17898,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____17917 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____17942  ->
      fun quals  ->
        match uu____17942 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18018 = FStar_Util.first_N nbinders formals in
              match uu____18018 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18099  ->
                         fun uu____18100  ->
                           match (uu____18099, uu____18100) with
                           | ((formal,uu____18118),(binder,uu____18120)) ->
                               let uu____18129 =
                                 let uu____18136 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18136) in
                               FStar_Syntax_Syntax.NT uu____18129) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18144 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18175  ->
                              match uu____18175 with
                              | (x,i) ->
                                  let uu____18186 =
                                    let uu___151_18187 = x in
                                    let uu____18188 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___151_18187.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___151_18187.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18188
                                    } in
                                  (uu____18186, i))) in
                    FStar_All.pipe_right uu____18144
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18206 =
                      let uu____18207 = FStar_Syntax_Subst.compress body in
                      let uu____18208 =
                        let uu____18209 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18209 in
                      FStar_Syntax_Syntax.extend_app_n uu____18207
                        uu____18208 in
                    uu____18206 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18270 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18270
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___152_18273 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___152_18273.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___152_18273.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___152_18273.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___152_18273.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___152_18273.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___152_18273.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___152_18273.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___152_18273.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___152_18273.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___152_18273.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___152_18273.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___152_18273.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___152_18273.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___152_18273.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___152_18273.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___152_18273.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___152_18273.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___152_18273.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___152_18273.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___152_18273.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___152_18273.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.type_of =
                         (uu___152_18273.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___152_18273.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___152_18273.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___152_18273.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___152_18273.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___152_18273.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___152_18273.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___152_18273.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18306 = FStar_Syntax_Util.abs_formals e in
                match uu____18306 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18370::uu____18371 ->
                         let uu____18386 =
                           let uu____18387 =
                             let uu____18390 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18390 in
                           uu____18387.FStar_Syntax_Syntax.n in
                         (match uu____18386 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18433 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18433 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18475 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18475
                                   then
                                     let uu____18510 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18510 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18604  ->
                                                   fun uu____18605  ->
                                                     match (uu____18604,
                                                             uu____18605)
                                                     with
                                                     | ((x,uu____18623),
                                                        (b,uu____18625)) ->
                                                         let uu____18634 =
                                                           let uu____18641 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18641) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18634)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18643 =
                                            let uu____18664 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18664) in
                                          (uu____18643, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18732 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18732 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18821) ->
                              let uu____18826 =
                                let uu____18847 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18847 in
                              (uu____18826, true)
                          | uu____18912 when Prims.op_Negation norm1 ->
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
                          | uu____18914 ->
                              let uu____18915 =
                                let uu____18916 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____18917 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____18916
                                  uu____18917 in
                              failwith uu____18915)
                     | uu____18942 ->
                         let uu____18943 =
                           let uu____18944 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____18944.FStar_Syntax_Syntax.n in
                         (match uu____18943 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18989 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18989 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19021 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19021 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19104 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19160 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19160
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19172 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19266  ->
                            fun lb  ->
                              match uu____19266 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19361 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19361
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19364 =
                                      let uu____19379 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19379
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19364 with
                                    | (tok,decl,env2) ->
                                        let uu____19425 =
                                          let uu____19438 =
                                            let uu____19449 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19449, tok) in
                                          uu____19438 :: toks in
                                        (uu____19425, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19172 with
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
                        | uu____19632 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19640 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19640 vars)
                            else
                              (let uu____19642 =
                                 let uu____19649 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19649) in
                               FStar_SMTEncoding_Util.mkApp uu____19642) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19731;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19733;
                             FStar_Syntax_Syntax.lbeff = uu____19734;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19797 =
                              let uu____19804 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19804 with
                              | (tcenv',uu____19822,e_t) ->
                                  let uu____19828 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19839 -> failwith "Impossible" in
                                  (match uu____19828 with
                                   | (e1,t_norm1) ->
                                       ((let uu___155_19855 = env2 in
                                         {
                                           bindings =
                                             (uu___155_19855.bindings);
                                           depth = (uu___155_19855.depth);
                                           tcenv = tcenv';
                                           warn = (uu___155_19855.warn);
                                           cache = (uu___155_19855.cache);
                                           nolabels =
                                             (uu___155_19855.nolabels);
                                           use_zfuel_name =
                                             (uu___155_19855.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___155_19855.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___155_19855.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19797 with
                             | (env',e1,t_norm1) ->
                                 let uu____19865 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____19865 with
                                  | ((binders,body,uu____19886,uu____19887),curry)
                                      ->
                                      ((let uu____19898 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____19898
                                        then
                                          let uu____19899 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____19900 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____19899 uu____19900
                                        else ());
                                       (let uu____19902 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____19902 with
                                        | (vars,guards,env'1,binder_decls,uu____19929)
                                            ->
                                            let body1 =
                                              let uu____19943 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____19943
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____19946 =
                                              let uu____19955 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____19955
                                              then
                                                let uu____19966 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____19967 =
                                                  encode_formula body1 env'1 in
                                                (uu____19966, uu____19967)
                                              else
                                                (let uu____19977 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____19977)) in
                                            (match uu____19946 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20000 =
                                                     let uu____20007 =
                                                       let uu____20008 =
                                                         let uu____20019 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20019) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20008 in
                                                     let uu____20030 =
                                                       let uu____20033 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20033 in
                                                     (uu____20007,
                                                       uu____20030,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20000 in
                                                 let uu____20036 =
                                                   let uu____20039 =
                                                     let uu____20042 =
                                                       let uu____20045 =
                                                         let uu____20048 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20048 in
                                                       FStar_List.append
                                                         decls2 uu____20045 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20042 in
                                                   FStar_List.append decls1
                                                     uu____20039 in
                                                 (uu____20036, env2))))))
                        | uu____20053 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20138 = varops.fresh "fuel" in
                          (uu____20138, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20141 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20229  ->
                                  fun uu____20230  ->
                                    match (uu____20229, uu____20230) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20378 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20378 in
                                        let gtok =
                                          let uu____20380 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20380 in
                                        let env4 =
                                          let uu____20382 =
                                            let uu____20385 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_44  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_44) uu____20385 in
                                          push_free_var env3 flid gtok
                                            uu____20382 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20141 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20541 t_norm
                              uu____20543 =
                              match (uu____20541, uu____20543) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20587;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20588;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20616 =
                                    let uu____20623 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20623 with
                                    | (tcenv',uu____20645,e_t) ->
                                        let uu____20651 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20662 ->
                                              failwith "Impossible" in
                                        (match uu____20651 with
                                         | (e1,t_norm1) ->
                                             ((let uu___156_20678 = env3 in
                                               {
                                                 bindings =
                                                   (uu___156_20678.bindings);
                                                 depth =
                                                   (uu___156_20678.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___156_20678.warn);
                                                 cache =
                                                   (uu___156_20678.cache);
                                                 nolabels =
                                                   (uu___156_20678.nolabels);
                                                 use_zfuel_name =
                                                   (uu___156_20678.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___156_20678.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___156_20678.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20616 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20693 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20693
                                         then
                                           let uu____20694 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20695 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20696 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20694 uu____20695
                                             uu____20696
                                         else ());
                                        (let uu____20698 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20698 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20735 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20735
                                               then
                                                 let uu____20736 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20737 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20738 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20739 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20736 uu____20737
                                                   uu____20738 uu____20739
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20743 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20743 with
                                               | (vars,guards,env'1,binder_decls,uu____20774)
                                                   ->
                                                   let decl_g =
                                                     let uu____20788 =
                                                       let uu____20799 =
                                                         let uu____20802 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20802 in
                                                       (g, uu____20799,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20788 in
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
                                                     let uu____20827 =
                                                       let uu____20834 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20834) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20827 in
                                                   let gsapp =
                                                     let uu____20844 =
                                                       let uu____20851 =
                                                         let uu____20854 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____20854 ::
                                                           vars_tm in
                                                       (g, uu____20851) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20844 in
                                                   let gmax =
                                                     let uu____20860 =
                                                       let uu____20867 =
                                                         let uu____20870 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____20870 ::
                                                           vars_tm in
                                                       (g, uu____20867) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20860 in
                                                   let body1 =
                                                     let uu____20876 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____20876
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____20878 =
                                                     encode_term body1 env'1 in
                                                   (match uu____20878 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____20896 =
                                                            let uu____20903 =
                                                              let uu____20904
                                                                =
                                                                let uu____20919
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
                                                                  uu____20919) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____20904 in
                                                            let uu____20940 =
                                                              let uu____20943
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____20943 in
                                                            (uu____20903,
                                                              uu____20940,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20896 in
                                                        let eqn_f =
                                                          let uu____20947 =
                                                            let uu____20954 =
                                                              let uu____20955
                                                                =
                                                                let uu____20966
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____20966) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20955 in
                                                            (uu____20954,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20947 in
                                                        let eqn_g' =
                                                          let uu____20980 =
                                                            let uu____20987 =
                                                              let uu____20988
                                                                =
                                                                let uu____20999
                                                                  =
                                                                  let uu____21000
                                                                    =
                                                                    let uu____21005
                                                                    =
                                                                    let uu____21006
                                                                    =
                                                                    let uu____21013
                                                                    =
                                                                    let uu____21016
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21016
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21013) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21006 in
                                                                    (gsapp,
                                                                    uu____21005) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21000 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____20999) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____20988 in
                                                            (uu____20987,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____20980 in
                                                        let uu____21039 =
                                                          let uu____21048 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21048
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21077)
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
                                                                  let uu____21102
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21102
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21107
                                                                  =
                                                                  let uu____21114
                                                                    =
                                                                    let uu____21115
                                                                    =
                                                                    let uu____21126
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21126) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21115 in
                                                                  (uu____21114,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21107 in
                                                              let uu____21147
                                                                =
                                                                let uu____21154
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21154
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21167
                                                                    =
                                                                    let uu____21170
                                                                    =
                                                                    let uu____21171
                                                                    =
                                                                    let uu____21178
                                                                    =
                                                                    let uu____21179
                                                                    =
                                                                    let uu____21190
                                                                    =
                                                                    let uu____21191
                                                                    =
                                                                    let uu____21196
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21196,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21191 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21190) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21179 in
                                                                    (uu____21178,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21171 in
                                                                    [uu____21170] in
                                                                    (d3,
                                                                    uu____21167) in
                                                              (match uu____21147
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21039
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
                            let uu____21261 =
                              let uu____21274 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21353  ->
                                   fun uu____21354  ->
                                     match (uu____21353, uu____21354) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21509 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21509 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21274 in
                            (match uu____21261 with
                             | (decls2,eqns,env01) ->
                                 let uu____21582 =
                                   let isDeclFun uu___122_21594 =
                                     match uu___122_21594 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21595 -> true
                                     | uu____21606 -> false in
                                   let uu____21607 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21607
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21582 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21647 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___123_21651  ->
                                 match uu___123_21651 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21652 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21658 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21658))) in
                      if uu____21647
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
                   let uu____21710 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21710
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
        let uu____21759 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21759 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21763 = encode_sigelt' env se in
      match uu____21763 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21779 =
                  let uu____21780 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21780 in
                [uu____21779]
            | uu____21781 ->
                let uu____21782 =
                  let uu____21785 =
                    let uu____21786 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21786 in
                  uu____21785 :: g in
                let uu____21787 =
                  let uu____21790 =
                    let uu____21791 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21791 in
                  [uu____21790] in
                FStar_List.append uu____21782 uu____21787 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21804 =
          let uu____21805 = FStar_Syntax_Subst.compress t in
          uu____21805.FStar_Syntax_Syntax.n in
        match uu____21804 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21809)) -> s = "opaque_to_smt"
        | uu____21810 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21815 =
          let uu____21816 = FStar_Syntax_Subst.compress t in
          uu____21816.FStar_Syntax_Syntax.n in
        match uu____21815 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21820)) -> s = "uninterpreted_by_smt"
        | uu____21821 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21826 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21831 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21834 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21837 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____21852 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____21856 =
            let uu____21857 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____21857 Prims.op_Negation in
          if uu____21856
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____21883 ->
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
               let uu____21903 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____21903 with
               | (aname,atok,env2) ->
                   let uu____21919 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____21919 with
                    | (formals,uu____21937) ->
                        let uu____21950 =
                          let uu____21955 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____21955 env2 in
                        (match uu____21950 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____21967 =
                                 let uu____21968 =
                                   let uu____21979 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____21995  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____21979,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____21968 in
                               [uu____21967;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22008 =
                               let aux uu____22060 uu____22061 =
                                 match (uu____22060, uu____22061) with
                                 | ((bv,uu____22113),(env3,acc_sorts,acc)) ->
                                     let uu____22151 = gen_term_var env3 bv in
                                     (match uu____22151 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22008 with
                              | (uu____22223,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22246 =
                                      let uu____22253 =
                                        let uu____22254 =
                                          let uu____22265 =
                                            let uu____22266 =
                                              let uu____22271 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22271) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22266 in
                                          ([[app]], xs_sorts, uu____22265) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22254 in
                                      (uu____22253,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22246 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22291 =
                                      let uu____22298 =
                                        let uu____22299 =
                                          let uu____22310 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22310) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22299 in
                                      (uu____22298,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22291 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22329 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22329 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22357,uu____22358)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22359 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22359 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22376,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22382 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___124_22386  ->
                      match uu___124_22386 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22387 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22392 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22393 -> false)) in
            Prims.op_Negation uu____22382 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22402 =
               let uu____22409 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22409 env fv t quals in
             match uu____22402 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22424 =
                   let uu____22427 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22427 in
                 (uu____22424, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22435 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22435 with
           | (uu____22444,f1) ->
               let uu____22446 = encode_formula f1 env in
               (match uu____22446 with
                | (f2,decls) ->
                    let g =
                      let uu____22460 =
                        let uu____22461 =
                          let uu____22468 =
                            let uu____22471 =
                              let uu____22472 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22472 in
                            FStar_Pervasives_Native.Some uu____22471 in
                          let uu____22473 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22468, uu____22473) in
                        FStar_SMTEncoding_Util.mkAssume uu____22461 in
                      [uu____22460] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22479) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22491 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22509 =
                       let uu____22512 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22512.FStar_Syntax_Syntax.fv_name in
                     uu____22509.FStar_Syntax_Syntax.v in
                   let uu____22513 =
                     let uu____22514 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22514 in
                   if uu____22513
                   then
                     let val_decl =
                       let uu___159_22542 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___159_22542.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___159_22542.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___159_22542.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22547 = encode_sigelt' env1 val_decl in
                     match uu____22547 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22491 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22575,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22577;
                          FStar_Syntax_Syntax.lbtyp = uu____22578;
                          FStar_Syntax_Syntax.lbeff = uu____22579;
                          FStar_Syntax_Syntax.lbdef = uu____22580;_}::[]),uu____22581)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22600 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22600 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22629 =
                   let uu____22632 =
                     let uu____22633 =
                       let uu____22640 =
                         let uu____22641 =
                           let uu____22652 =
                             let uu____22653 =
                               let uu____22658 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22658) in
                             FStar_SMTEncoding_Util.mkEq uu____22653 in
                           ([[b2t_x]], [xx], uu____22652) in
                         FStar_SMTEncoding_Util.mkForall uu____22641 in
                       (uu____22640,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22633 in
                   [uu____22632] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22629 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22691,uu____22692) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_22701  ->
                  match uu___125_22701 with
                  | FStar_Syntax_Syntax.Discriminator uu____22702 -> true
                  | uu____22703 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22706,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22717 =
                     let uu____22718 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22718.FStar_Ident.idText in
                   uu____22717 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___126_22722  ->
                     match uu___126_22722 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22723 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22727) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___127_22744  ->
                  match uu___127_22744 with
                  | FStar_Syntax_Syntax.Projector uu____22745 -> true
                  | uu____22750 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22753 = try_lookup_free_var env l in
          (match uu____22753 with
           | FStar_Pervasives_Native.Some uu____22760 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___160_22764 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___160_22764.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___160_22764.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___160_22764.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22771) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22789) ->
          let uu____22798 = encode_sigelts env ses in
          (match uu____22798 with
           | (g,env1) ->
               let uu____22815 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___128_22838  ->
                         match uu___128_22838 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22839;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22840;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22841;_}
                             -> false
                         | uu____22844 -> true)) in
               (match uu____22815 with
                | (g',inversions) ->
                    let uu____22859 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___129_22880  ->
                              match uu___129_22880 with
                              | FStar_SMTEncoding_Term.DeclFun uu____22881 ->
                                  true
                              | uu____22892 -> false)) in
                    (match uu____22859 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____22910,tps,k,uu____22913,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___130_22930  ->
                    match uu___130_22930 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____22931 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____22940 = c in
              match uu____22940 with
              | (name,args,uu____22945,uu____22946,uu____22947) ->
                  let uu____22952 =
                    let uu____22953 =
                      let uu____22964 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____22981  ->
                                match uu____22981 with
                                | (uu____22988,sort,uu____22990) -> sort)) in
                      (name, uu____22964, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____22953 in
                  [uu____22952]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23017 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23023 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23023 FStar_Option.isNone)) in
            if uu____23017
            then []
            else
              (let uu____23055 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23055 with
               | (xxsym,xx) ->
                   let uu____23064 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23103  ->
                             fun l  ->
                               match uu____23103 with
                               | (out,decls) ->
                                   let uu____23123 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23123 with
                                    | (uu____23134,data_t) ->
                                        let uu____23136 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23136 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23182 =
                                                 let uu____23183 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23183.FStar_Syntax_Syntax.n in
                                               match uu____23182 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23194,indices) ->
                                                   indices
                                               | uu____23216 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23240  ->
                                                         match uu____23240
                                                         with
                                                         | (x,uu____23246) ->
                                                             let uu____23247
                                                               =
                                                               let uu____23248
                                                                 =
                                                                 let uu____23255
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23255,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23248 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23247)
                                                    env) in
                                             let uu____23258 =
                                               encode_args indices env1 in
                                             (match uu____23258 with
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
                                                      let uu____23284 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23300
                                                                 =
                                                                 let uu____23305
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23305,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23300)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23284
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23308 =
                                                      let uu____23309 =
                                                        let uu____23314 =
                                                          let uu____23315 =
                                                            let uu____23320 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23320,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23315 in
                                                        (out, uu____23314) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23309 in
                                                    (uu____23308,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23064 with
                    | (data_ax,decls) ->
                        let uu____23333 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23333 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23344 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23344 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23348 =
                                 let uu____23355 =
                                   let uu____23356 =
                                     let uu____23367 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23382 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23367,
                                       uu____23382) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23356 in
                                 let uu____23397 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23355,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23397) in
                               FStar_SMTEncoding_Util.mkAssume uu____23348 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23400 =
            let uu____23413 =
              let uu____23414 = FStar_Syntax_Subst.compress k in
              uu____23414.FStar_Syntax_Syntax.n in
            match uu____23413 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23459 -> (tps, k) in
          (match uu____23400 with
           | (formals,res) ->
               let uu____23482 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23482 with
                | (formals1,res1) ->
                    let uu____23493 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23493 with
                     | (vars,guards,env',binder_decls,uu____23518) ->
                         let uu____23531 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23531 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23550 =
                                  let uu____23557 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23557) in
                                FStar_SMTEncoding_Util.mkApp uu____23550 in
                              let uu____23566 =
                                let tname_decl =
                                  let uu____23576 =
                                    let uu____23577 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23609  ->
                                              match uu____23609 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23622 = varops.next_id () in
                                    (tname, uu____23577,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23622, false) in
                                  constructor_or_logic_type_decl uu____23576 in
                                let uu____23631 =
                                  match vars with
                                  | [] ->
                                      let uu____23644 =
                                        let uu____23645 =
                                          let uu____23648 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____23648 in
                                        push_free_var env1 t tname
                                          uu____23645 in
                                      ([], uu____23644)
                                  | uu____23655 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23664 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23664 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23678 =
                                          let uu____23685 =
                                            let uu____23686 =
                                              let uu____23701 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23701) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23686 in
                                          (uu____23685,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23678 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23631 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23566 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23741 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23741 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23759 =
                                               let uu____23760 =
                                                 let uu____23767 =
                                                   let uu____23768 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23768 in
                                                 (uu____23767,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23760 in
                                             [uu____23759]
                                           else [] in
                                         let uu____23772 =
                                           let uu____23775 =
                                             let uu____23778 =
                                               let uu____23779 =
                                                 let uu____23786 =
                                                   let uu____23787 =
                                                     let uu____23798 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23798) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23787 in
                                                 (uu____23786,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23779 in
                                             [uu____23778] in
                                           FStar_List.append karr uu____23775 in
                                         FStar_List.append decls1 uu____23772 in
                                   let aux =
                                     let uu____23814 =
                                       let uu____23817 =
                                         inversion_axioms tapp vars in
                                       let uu____23820 =
                                         let uu____23823 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23823] in
                                       FStar_List.append uu____23817
                                         uu____23820 in
                                     FStar_List.append kindingAx uu____23814 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23830,uu____23831,uu____23832,uu____23833,uu____23834)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23842,t,uu____23844,n_tps,uu____23846) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____23854 = new_term_constant_and_tok_from_lid env d in
          (match uu____23854 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____23871 = FStar_Syntax_Util.arrow_formals t in
               (match uu____23871 with
                | (formals,t_res) ->
                    let uu____23906 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____23906 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____23920 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____23920 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____23990 =
                                            mk_term_projector_name d x in
                                          (uu____23990,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____23992 =
                                  let uu____24011 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24011, true) in
                                FStar_All.pipe_right uu____23992
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
                              let uu____24050 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24050 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24062::uu____24063 ->
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
                                         let uu____24108 =
                                           let uu____24119 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24119) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24108
                                     | uu____24144 -> tok_typing in
                                   let uu____24153 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24153 with
                                    | (vars',guards',env'',decls_formals,uu____24178)
                                        ->
                                        let uu____24191 =
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
                                        (match uu____24191 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24222 ->
                                                   let uu____24229 =
                                                     let uu____24230 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24230 in
                                                   [uu____24229] in
                                             let encode_elim uu____24240 =
                                               let uu____24241 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24241 with
                                               | (head1,args) ->
                                                   let uu____24284 =
                                                     let uu____24285 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24285.FStar_Syntax_Syntax.n in
                                                   (match uu____24284 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24295;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24296;_},uu____24297)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24303 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24303
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
                                                                 | uu____24346
                                                                    ->
                                                                    let uu____24347
                                                                    =
                                                                    let uu____24348
                                                                    =
                                                                    let uu____24353
                                                                    =
                                                                    let uu____24354
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24354 in
                                                                    (uu____24353,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24348 in
                                                                    FStar_Exn.raise
                                                                    uu____24347 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24370
                                                                    =
                                                                    let uu____24371
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24371 in
                                                                    if
                                                                    uu____24370
                                                                    then
                                                                    let uu____24384
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24384]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24386
                                                               =
                                                               let uu____24399
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24449
                                                                     ->
                                                                    fun
                                                                    uu____24450
                                                                     ->
                                                                    match 
                                                                    (uu____24449,
                                                                    uu____24450)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24545
                                                                    =
                                                                    let uu____24552
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24552 in
                                                                    (match uu____24545
                                                                    with
                                                                    | 
                                                                    (uu____24565,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24573
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24573
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24575
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24575
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
                                                                 uu____24399 in
                                                             (match uu____24386
                                                              with
                                                              | (uu____24590,arg_vars,elim_eqns_or_guards,uu____24593)
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
                                                                    let uu____24623
                                                                    =
                                                                    let uu____24630
                                                                    =
                                                                    let uu____24631
                                                                    =
                                                                    let uu____24642
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24653
                                                                    =
                                                                    let uu____24654
                                                                    =
                                                                    let uu____24659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24659) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24654 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24642,
                                                                    uu____24653) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24631 in
                                                                    (uu____24630,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24623 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24682
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24682,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24684
                                                                    =
                                                                    let uu____24691
                                                                    =
                                                                    let uu____24692
                                                                    =
                                                                    let uu____24703
                                                                    =
                                                                    let uu____24708
                                                                    =
                                                                    let uu____24711
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24711] in
                                                                    [uu____24708] in
                                                                    let uu____24716
                                                                    =
                                                                    let uu____24717
                                                                    =
                                                                    let uu____24722
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24723
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24722,
                                                                    uu____24723) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24717 in
                                                                    (uu____24703,
                                                                    [x],
                                                                    uu____24716) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24692 in
                                                                    let uu____24742
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24691,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24742) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24684
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24749
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
                                                                    (let uu____24777
                                                                    =
                                                                    let uu____24778
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24778
                                                                    dapp1 in
                                                                    [uu____24777]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24749
                                                                    FStar_List.flatten in
                                                                    let uu____24785
                                                                    =
                                                                    let uu____24792
                                                                    =
                                                                    let uu____24793
                                                                    =
                                                                    let uu____24804
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24815
                                                                    =
                                                                    let uu____24816
                                                                    =
                                                                    let uu____24821
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24821) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24816 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24804,
                                                                    uu____24815) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24793 in
                                                                    (uu____24792,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24785) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24842 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24842
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
                                                                 | uu____24885
                                                                    ->
                                                                    let uu____24886
                                                                    =
                                                                    let uu____24887
                                                                    =
                                                                    let uu____24892
                                                                    =
                                                                    let uu____24893
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24893 in
                                                                    (uu____24892,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24887 in
                                                                    FStar_Exn.raise
                                                                    uu____24886 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24909
                                                                    =
                                                                    let uu____24910
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24910 in
                                                                    if
                                                                    uu____24909
                                                                    then
                                                                    let uu____24923
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24923]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24925
                                                               =
                                                               let uu____24938
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24988
                                                                     ->
                                                                    fun
                                                                    uu____24989
                                                                     ->
                                                                    match 
                                                                    (uu____24988,
                                                                    uu____24989)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25084
                                                                    =
                                                                    let uu____25091
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25091 in
                                                                    (match uu____25084
                                                                    with
                                                                    | 
                                                                    (uu____25104,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25112
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25112
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25114
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25114
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
                                                                 uu____24938 in
                                                             (match uu____24925
                                                              with
                                                              | (uu____25129,arg_vars,elim_eqns_or_guards,uu____25132)
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
                                                                    let uu____25162
                                                                    =
                                                                    let uu____25169
                                                                    =
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25181
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25192
                                                                    =
                                                                    let uu____25193
                                                                    =
                                                                    let uu____25198
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25198) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25193 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25181,
                                                                    uu____25192) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25170 in
                                                                    (uu____25169,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25162 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25221
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25221,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25223
                                                                    =
                                                                    let uu____25230
                                                                    =
                                                                    let uu____25231
                                                                    =
                                                                    let uu____25242
                                                                    =
                                                                    let uu____25247
                                                                    =
                                                                    let uu____25250
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25250] in
                                                                    [uu____25247] in
                                                                    let uu____25255
                                                                    =
                                                                    let uu____25256
                                                                    =
                                                                    let uu____25261
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25262
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25261,
                                                                    uu____25262) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25256 in
                                                                    (uu____25242,
                                                                    [x],
                                                                    uu____25255) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25231 in
                                                                    let uu____25281
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25230,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25281) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25223
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25288
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
                                                                    (let uu____25316
                                                                    =
                                                                    let uu____25317
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25317
                                                                    dapp1 in
                                                                    [uu____25316]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25288
                                                                    FStar_List.flatten in
                                                                    let uu____25324
                                                                    =
                                                                    let uu____25331
                                                                    =
                                                                    let uu____25332
                                                                    =
                                                                    let uu____25343
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25354
                                                                    =
                                                                    let uu____25355
                                                                    =
                                                                    let uu____25360
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25360) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25355 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25343,
                                                                    uu____25354) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25332 in
                                                                    (uu____25331,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25324) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25379 ->
                                                        ((let uu____25381 =
                                                            let uu____25382 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25383 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25382
                                                              uu____25383 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25381);
                                                         ([], []))) in
                                             let uu____25388 = encode_elim () in
                                             (match uu____25388 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25408 =
                                                      let uu____25411 =
                                                        let uu____25414 =
                                                          let uu____25417 =
                                                            let uu____25420 =
                                                              let uu____25421
                                                                =
                                                                let uu____25432
                                                                  =
                                                                  let uu____25435
                                                                    =
                                                                    let uu____25436
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25436 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25435 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25432) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25421 in
                                                            [uu____25420] in
                                                          let uu____25441 =
                                                            let uu____25444 =
                                                              let uu____25447
                                                                =
                                                                let uu____25450
                                                                  =
                                                                  let uu____25453
                                                                    =
                                                                    let uu____25456
                                                                    =
                                                                    let uu____25459
                                                                    =
                                                                    let uu____25460
                                                                    =
                                                                    let uu____25467
                                                                    =
                                                                    let uu____25468
                                                                    =
                                                                    let uu____25479
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25479) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25468 in
                                                                    (uu____25467,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25460 in
                                                                    let uu____25492
                                                                    =
                                                                    let uu____25495
                                                                    =
                                                                    let uu____25496
                                                                    =
                                                                    let uu____25503
                                                                    =
                                                                    let uu____25504
                                                                    =
                                                                    let uu____25515
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25526
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25515,
                                                                    uu____25526) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25504 in
                                                                    (uu____25503,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25496 in
                                                                    [uu____25495] in
                                                                    uu____25459
                                                                    ::
                                                                    uu____25492 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25456 in
                                                                  FStar_List.append
                                                                    uu____25453
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25450 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25447 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25444 in
                                                          FStar_List.append
                                                            uu____25417
                                                            uu____25441 in
                                                        FStar_List.append
                                                          decls3 uu____25414 in
                                                      FStar_List.append
                                                        decls2 uu____25411 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25408 in
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
           (fun uu____25572  ->
              fun se  ->
                match uu____25572 with
                | (g,env1) ->
                    let uu____25592 = encode_sigelt env1 se in
                    (match uu____25592 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25651 =
        match uu____25651 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25683 ->
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
                 ((let uu____25689 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25689
                   then
                     let uu____25690 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25691 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25692 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25690 uu____25691 uu____25692
                   else ());
                  (let uu____25694 = encode_term t1 env1 in
                   match uu____25694 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25710 =
                         let uu____25717 =
                           let uu____25718 =
                             let uu____25719 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25719
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25718 in
                         new_term_constant_from_string env1 x uu____25717 in
                       (match uu____25710 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25735 = FStar_Options.log_queries () in
                              if uu____25735
                              then
                                let uu____25738 =
                                  let uu____25739 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25740 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25741 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25739 uu____25740 uu____25741 in
                                FStar_Pervasives_Native.Some uu____25738
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25757,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25771 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25771 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25794,se,uu____25796) ->
                 let uu____25801 = encode_sigelt env1 se in
                 (match uu____25801 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25818,se) ->
                 let uu____25824 = encode_sigelt env1 se in
                 (match uu____25824 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25841 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25841 with | (uu____25864,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____25879 'Auu____25880 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____25880,'Auu____25879)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____25948  ->
              match uu____25948 with
              | (l,uu____25960,uu____25961) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26007  ->
              match uu____26007 with
              | (l,uu____26021,uu____26022) ->
                  let uu____26031 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26032 =
                    let uu____26035 =
                      let uu____26036 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26036 in
                    [uu____26035] in
                  uu____26031 :: uu____26032)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26058 =
      let uu____26061 =
        let uu____26062 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26065 =
          let uu____26066 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26066 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26062;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26065
        } in
      [uu____26061] in
    FStar_ST.op_Colon_Equals last_env uu____26058
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26093 = FStar_ST.op_Bang last_env in
      match uu____26093 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26115 ->
          let uu___161_26118 = e in
          let uu____26119 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___161_26118.bindings);
            depth = (uu___161_26118.depth);
            tcenv;
            warn = (uu___161_26118.warn);
            cache = (uu___161_26118.cache);
            nolabels = (uu___161_26118.nolabels);
            use_zfuel_name = (uu___161_26118.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___161_26118.encode_non_total_function_typ);
            current_module_name = uu____26119
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26124 = FStar_ST.op_Bang last_env in
    match uu____26124 with
    | [] -> failwith "Empty env stack"
    | uu____26145::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26170  ->
    let uu____26171 = FStar_ST.op_Bang last_env in
    match uu____26171 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___162_26200 = hd1 in
          {
            bindings = (uu___162_26200.bindings);
            depth = (uu___162_26200.depth);
            tcenv = (uu___162_26200.tcenv);
            warn = (uu___162_26200.warn);
            cache = refs;
            nolabels = (uu___162_26200.nolabels);
            use_zfuel_name = (uu___162_26200.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___162_26200.encode_non_total_function_typ);
            current_module_name = (uu___162_26200.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26222  ->
    let uu____26223 = FStar_ST.op_Bang last_env in
    match uu____26223 with
    | [] -> failwith "Popping an empty stack"
    | uu____26244::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26310::uu____26311,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___163_26319 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___163_26319.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___163_26319.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___163_26319.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26320 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26337 =
        let uu____26340 =
          let uu____26341 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26341 in
        let uu____26342 = open_fact_db_tags env in uu____26340 :: uu____26342 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26337
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
      let uu____26366 = encode_sigelt env se in
      match uu____26366 with
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
        let uu____26404 = FStar_Options.log_queries () in
        if uu____26404
        then
          let uu____26407 =
            let uu____26408 =
              let uu____26409 =
                let uu____26410 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26410 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26409 in
            FStar_SMTEncoding_Term.Caption uu____26408 in
          uu____26407 :: decls
        else decls in
      let env =
        let uu____26421 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26421 tcenv in
      let uu____26422 = encode_top_level_facts env se in
      match uu____26422 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26436 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____26436))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26450 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26450
       then
         let uu____26451 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26451
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26486  ->
                 fun se  ->
                   match uu____26486 with
                   | (g,env2) ->
                       let uu____26506 = encode_top_level_facts env2 se in
                       (match uu____26506 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26529 =
         encode_signature
           (let uu___164_26538 = env in
            {
              bindings = (uu___164_26538.bindings);
              depth = (uu___164_26538.depth);
              tcenv = (uu___164_26538.tcenv);
              warn = false;
              cache = (uu___164_26538.cache);
              nolabels = (uu___164_26538.nolabels);
              use_zfuel_name = (uu___164_26538.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___164_26538.encode_non_total_function_typ);
              current_module_name = (uu___164_26538.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26529 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26555 = FStar_Options.log_queries () in
             if uu____26555
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___165_26563 = env1 in
               {
                 bindings = (uu___165_26563.bindings);
                 depth = (uu___165_26563.depth);
                 tcenv = (uu___165_26563.tcenv);
                 warn = true;
                 cache = (uu___165_26563.cache);
                 nolabels = (uu___165_26563.nolabels);
                 use_zfuel_name = (uu___165_26563.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___165_26563.encode_non_total_function_typ);
                 current_module_name = (uu___165_26563.current_module_name)
               });
            (let uu____26565 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26565
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
        (let uu____26620 =
           let uu____26621 = FStar_TypeChecker_Env.current_module tcenv in
           uu____26621.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26620);
        (let env =
           let uu____26623 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____26623 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____26635 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____26670 = aux rest in
                 (match uu____26670 with
                  | (out,rest1) ->
                      let t =
                        let uu____26700 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____26700 with
                        | FStar_Pervasives_Native.Some uu____26705 ->
                            let uu____26706 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____26706
                              x.FStar_Syntax_Syntax.sort
                        | uu____26707 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____26711 =
                        let uu____26714 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___166_26717 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___166_26717.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___166_26717.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____26714 :: out in
                      (uu____26711, rest1))
             | uu____26722 -> ([], bindings1) in
           let uu____26729 = aux bindings in
           match uu____26729 with
           | (closing,bindings1) ->
               let uu____26754 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____26754, bindings1) in
         match uu____26635 with
         | (q1,bindings1) ->
             let uu____26777 =
               let uu____26782 =
                 FStar_List.filter
                   (fun uu___131_26787  ->
                      match uu___131_26787 with
                      | FStar_TypeChecker_Env.Binding_sig uu____26788 ->
                          false
                      | uu____26795 -> true) bindings1 in
               encode_env_bindings env uu____26782 in
             (match uu____26777 with
              | (env_decls,env1) ->
                  ((let uu____26813 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____26813
                    then
                      let uu____26814 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____26814
                    else ());
                   (let uu____26816 = encode_formula q1 env1 in
                    match uu____26816 with
                    | (phi,qdecls) ->
                        let uu____26837 =
                          let uu____26842 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____26842 phi in
                        (match uu____26837 with
                         | (labels,phi1) ->
                             let uu____26859 = encode_labels labels in
                             (match uu____26859 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____26896 =
                                      let uu____26903 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____26904 =
                                        varops.mk_unique "@query" in
                                      (uu____26903,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____26904) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____26896 in
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
        let uu____26923 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____26923 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____26925 = encode_formula q env in
       match uu____26925 with
       | (f,uu____26931) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____26933) -> true
             | uu____26938 -> false)))