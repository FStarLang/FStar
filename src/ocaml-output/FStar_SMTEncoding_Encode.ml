open Prims
let add_fuel:
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives () in
      if uu____19 then tl1 else x :: tl1
let withenv:
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____30 ->
      ('Auu____29,'Auu____28) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____28,'Auu____30) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c)
let vargs:
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___364_107  ->
         match uu___364_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
let subst_lcomp_opt:
  'Auu____134 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____170 =
            let uu____175 =
              let uu____176 =
                let uu____179 = l1.FStar_Syntax_Syntax.comp () in
                FStar_Syntax_Subst.subst_comp s uu____179 in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____176 in
            FStar_Util.Inl uu____175 in
          FStar_Pervasives_Native.Some uu____170
      | uu____186 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___387_203 = a in
        let uu____204 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____204;
          FStar_Syntax_Syntax.index =
            (uu___387_203.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___387_203.FStar_Syntax_Syntax.sort)
        } in
      let uu____205 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____205
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____218 =
          let uu____219 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____219 in
        let uu____220 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____220 with
        | (uu____225,t) ->
            let uu____227 =
              let uu____228 = FStar_Syntax_Subst.compress t in
              uu____228.FStar_Syntax_Syntax.n in
            (match uu____227 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____249 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____249 with
                  | (binders,uu____255) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____270 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____277 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____277
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____284 =
        let uu____289 = mk_term_projector_name lid a in
        (uu____289,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____284
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____296 =
        let uu____301 = mk_term_projector_name_by_pos lid i in
        (uu____301,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____296
let mk_data_tester:
  'Auu____306 .
    'Auu____306 ->
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
  let new_scope uu____670 =
    let uu____671 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____674 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____671, uu____674) in
  let scopes =
    let uu____694 = let uu____705 = new_scope () in [uu____705] in
    FStar_Util.mk_ref uu____694 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____746 =
        let uu____749 = FStar_ST.op_Bang scopes in
        FStar_Util.find_map uu____749
          (fun uu____851  ->
             match uu____851 with
             | (names1,uu____863) -> FStar_Util.smap_try_find names1 y1) in
      match uu____746 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____872 ->
          (FStar_Util.incr ctr;
           (let uu____895 =
              let uu____896 =
                let uu____897 = FStar_ST.op_Bang ctr in
                Prims.string_of_int uu____897 in
              Prims.strcat "__" uu____896 in
            Prims.strcat y1 uu____895)) in
    let top_scope =
      let uu____961 =
        let uu____970 = FStar_ST.op_Bang scopes in FStar_List.hd uu____970 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____961 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1098 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr in
  let fresh1 pfx =
    let uu____1185 =
      let uu____1186 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1186 in
    FStar_Util.format2 "%s_%s" pfx uu____1185 in
  let string_const s =
    let uu____1191 =
      let uu____1194 = FStar_ST.op_Bang scopes in
      FStar_Util.find_map uu____1194
        (fun uu____1296  ->
           match uu____1296 with
           | (uu____1307,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1191 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1320 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1320 in
        let top_scope =
          let uu____1324 =
            let uu____1333 = FStar_ST.op_Bang scopes in
            FStar_List.hd uu____1333 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1324 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1450 =
    let uu____1451 =
      let uu____1462 = new_scope () in
      let uu____1471 = FStar_ST.op_Bang scopes in uu____1462 :: uu____1471 in
    FStar_ST.op_Colon_Equals scopes uu____1451 in
  let pop1 uu____1653 =
    let uu____1654 =
      let uu____1665 = FStar_ST.op_Bang scopes in FStar_List.tl uu____1665 in
    FStar_ST.op_Colon_Equals scopes uu____1654 in
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
    let uu___388_1847 = x in
    let uu____1848 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1848;
      FStar_Syntax_Syntax.index = (uu___388_1847.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___388_1847.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1881 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1917 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar:
  'Auu____1964 'Auu____1965 .
    'Auu____1965 ->
      ('Auu____1965,'Auu____1964 FStar_Pervasives_Native.option)
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
  'Auu____2261 .
    'Auu____2261 ->
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
                 (fun uu___365_2295  ->
                    match uu___365_2295 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2299 -> [])) in
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
    let uu____2308 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___366_2318  ->
              match uu___366_2318 with
              | Binding_var (x,uu____2320) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2322,uu____2323,uu____2324) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2308 (FStar_String.concat ", ")
let lookup_binding:
  'Auu____2338 .
    env_t ->
      (binding -> 'Auu____2338 FStar_Pervasives_Native.option) ->
        'Auu____2338 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2366 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2366
      then
        let uu____2369 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2369
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
      let uu____2382 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2382)
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
        (let uu___389_2398 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___389_2398.tcenv);
           warn = (uu___389_2398.warn);
           cache = (uu___389_2398.cache);
           nolabels = (uu___389_2398.nolabels);
           use_zfuel_name = (uu___389_2398.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___389_2398.encode_non_total_function_typ);
           current_module_name = (uu___389_2398.current_module_name)
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
        (let uu___390_2416 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___390_2416.depth);
           tcenv = (uu___390_2416.tcenv);
           warn = (uu___390_2416.warn);
           cache = (uu___390_2416.cache);
           nolabels = (uu___390_2416.nolabels);
           use_zfuel_name = (uu___390_2416.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___390_2416.encode_non_total_function_typ);
           current_module_name = (uu___390_2416.current_module_name)
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
          (let uu___391_2437 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___391_2437.depth);
             tcenv = (uu___391_2437.tcenv);
             warn = (uu___391_2437.warn);
             cache = (uu___391_2437.cache);
             nolabels = (uu___391_2437.nolabels);
             use_zfuel_name = (uu___391_2437.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___391_2437.encode_non_total_function_typ);
             current_module_name = (uu___391_2437.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___392_2447 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___392_2447.depth);
          tcenv = (uu___392_2447.tcenv);
          warn = (uu___392_2447.warn);
          cache = (uu___392_2447.cache);
          nolabels = (uu___392_2447.nolabels);
          use_zfuel_name = (uu___392_2447.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___392_2447.encode_non_total_function_typ);
          current_module_name = (uu___392_2447.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___367_2471  ->
             match uu___367_2471 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2484 -> FStar_Pervasives_Native.None) in
      let uu____2489 = aux a in
      match uu____2489 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2501 = aux a2 in
          (match uu____2501 with
           | FStar_Pervasives_Native.None  ->
               let uu____2512 =
                 let uu____2513 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2514 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2513 uu____2514 in
               failwith uu____2512
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
      let uu____2541 =
        let uu___393_2542 = env in
        let uu____2543 =
          let uu____2546 =
            let uu____2547 =
              let uu____2560 =
                let uu____2563 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2563 in
              (x, fname, uu____2560, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2547 in
          uu____2546 :: (env.bindings) in
        {
          bindings = uu____2543;
          depth = (uu___393_2542.depth);
          tcenv = (uu___393_2542.tcenv);
          warn = (uu___393_2542.warn);
          cache = (uu___393_2542.cache);
          nolabels = (uu___393_2542.nolabels);
          use_zfuel_name = (uu___393_2542.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___393_2542.encode_non_total_function_typ);
          current_module_name = (uu___393_2542.current_module_name)
        } in
      (fname, ftok, uu____2541)
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
        (fun uu___368_2605  ->
           match uu___368_2605 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2644 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2661 =
        lookup_binding env
          (fun uu___369_2669  ->
             match uu___369_2669 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2684 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2661 FStar_Option.isSome
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
      let uu____2703 = try_lookup_lid env a in
      match uu____2703 with
      | FStar_Pervasives_Native.None  ->
          let uu____2736 =
            let uu____2737 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2737 in
          failwith uu____2736
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
          let uu___394_2785 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___394_2785.depth);
            tcenv = (uu___394_2785.tcenv);
            warn = (uu___394_2785.warn);
            cache = (uu___394_2785.cache);
            nolabels = (uu___394_2785.nolabels);
            use_zfuel_name = (uu___394_2785.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___394_2785.encode_non_total_function_typ);
            current_module_name = (uu___394_2785.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2799 = lookup_lid env x in
        match uu____2799 with
        | (t1,t2,uu____2812) ->
            let t3 =
              let uu____2822 =
                let uu____2829 =
                  let uu____2832 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2832] in
                (f, uu____2829) in
              FStar_SMTEncoding_Util.mkApp uu____2822 in
            let uu___395_2837 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___395_2837.depth);
              tcenv = (uu___395_2837.tcenv);
              warn = (uu___395_2837.warn);
              cache = (uu___395_2837.cache);
              nolabels = (uu___395_2837.nolabels);
              use_zfuel_name = (uu___395_2837.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___395_2837.encode_non_total_function_typ);
              current_module_name = (uu___395_2837.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2850 = try_lookup_lid env l in
      match uu____2850 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2899 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2907,fuel::[]) ->
                         let uu____2911 =
                           let uu____2912 =
                             let uu____2913 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2913
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2912 "fuel" in
                         if uu____2911
                         then
                           let uu____2916 =
                             let uu____2917 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2917
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2916
                         else FStar_Pervasives_Native.Some t
                     | uu____2921 -> FStar_Pervasives_Native.Some t)
                | uu____2922 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2935 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2935 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2939 =
            let uu____2940 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2940 in
          failwith uu____2939
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2951 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2951 with | (x,uu____2963,uu____2964) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2989 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2989 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3025;
                 FStar_SMTEncoding_Term.rng = uu____3026;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3041 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3065 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___370_3081  ->
           match uu___370_3081 with
           | Binding_fvar (uu____3084,nm',tok,uu____3087) when nm = nm' ->
               tok
           | uu____3096 -> FStar_Pervasives_Native.None)
let mkForall_fuel':
  'Auu____3100 .
    'Auu____3100 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3118  ->
      match uu____3118 with
      | (pats,vars,body) ->
          let fallback uu____3143 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
          let uu____3148 = FStar_Options.unthrottle_inductives () in
          if uu____3148
          then fallback ()
          else
            (let uu____3150 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
             match uu____3150 with
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
                           | uu____3181 -> p)) in
                 let pats1 = FStar_List.map add_fuel1 pats in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3202 = add_fuel1 guards in
                             FStar_SMTEncoding_Util.mk_and_l uu____3202
                         | uu____3205 ->
                             let uu____3206 = add_fuel1 [guard] in
                             FStar_All.pipe_right uu____3206 FStar_List.hd in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3211 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3252 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3265 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3272 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3273 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3290 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3307 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3309 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3309 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3327;
             FStar_Syntax_Syntax.vars = uu____3328;_},uu____3329)
          ->
          let uu____3350 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3350 FStar_Option.isNone
      | uu____3367 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3374 =
        let uu____3375 = FStar_Syntax_Util.un_uinst t in
        uu____3375.FStar_Syntax_Syntax.n in
      match uu____3374 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3378,uu____3379,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___371_3400  ->
                  match uu___371_3400 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3401 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3403 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3403 FStar_Option.isSome
      | uu____3420 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3427 = head_normal env t in
      if uu____3427
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
    let uu____3438 =
      let uu____3439 = FStar_Syntax_Syntax.null_binder t in [uu____3439] in
    let uu____3440 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3438 uu____3440 FStar_Pervasives_Native.None
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
                    let uu____3478 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3478
                | s ->
                    let uu____3483 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3483) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___372_3498  ->
    match uu___372_3498 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3499 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3535;
                       FStar_SMTEncoding_Term.rng = uu____3536;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3559) ->
              let uu____3568 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3579 -> false) args (FStar_List.rev xs)) in
              if uu____3568
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3583,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3587 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3591 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3591)) in
              if uu____3587
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3595 -> FStar_Pervasives_Native.None in
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
    | uu____3817 -> false
exception Inner_let_rec
let uu___is_Inner_let_rec: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3821 -> false
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
        | FStar_Syntax_Syntax.Tm_arrow uu____3840 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3853 ->
            let uu____3860 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3860
        | uu____3861 ->
            if norm1
            then let uu____3862 = whnf env t1 in aux false uu____3862
            else
              (let uu____3864 =
                 let uu____3865 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3866 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3865 uu____3866 in
               failwith uu____3864) in
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
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3898) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3903 ->
        let uu____3904 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3904)
let is_arithmetic_primitive:
  'Auu____3918 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3918 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3938::uu____3939::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3943::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3946 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3967 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3982 -> failwith "Expected an Integer term"
let is_BitVector_primitive:
  'Auu____3986 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3986)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4025)::uu____4026::uu____4027::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4078)::uu____4079::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4116 -> false
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
          let uu____4323 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue in
          (uu____4323, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4326 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse in
          (uu____4326, [])
      | FStar_Const.Const_char c1 ->
          let uu____4330 =
            let uu____4331 =
              let uu____4338 =
                let uu____4341 =
                  let uu____4342 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1) in
                  FStar_SMTEncoding_Term.boxInt uu____4342 in
                [uu____4341] in
              ("FStar.Char.Char", uu____4338) in
            FStar_SMTEncoding_Util.mkApp uu____4331 in
          (uu____4330, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4358 =
            let uu____4359 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4359 in
          (uu____4358, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4380) ->
          let uu____4381 = varops.string_const s in (uu____4381, [])
      | FStar_Const.Const_range uu____4384 ->
          let uu____4385 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4385, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4391 =
            let uu____4392 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4392 in
          failwith uu____4391
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
        (let uu____4421 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4421
         then
           let uu____4422 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4422
         else ());
        (let uu____4424 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4508  ->
                   fun b  ->
                     match uu____4508 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4587 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4603 = gen_term_var env1 x in
                           match uu____4603 with
                           | (xxsym,xx,env') ->
                               let uu____4627 =
                                 let uu____4632 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4632 env1 xx in
                               (match uu____4627 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4587 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4424 with
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
          let uu____4791 = encode_term t env in
          match uu____4791 with
          | (t1,decls) ->
              let uu____4802 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4802, decls)
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
          let uu____4813 = encode_term t env in
          match uu____4813 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4828 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4828, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4830 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4830, decls))
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
        let uu____4836 = encode_args args_e env in
        match uu____4836 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4855 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4864 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4864 in
            let binary arg_tms1 =
              let uu____4877 =
                let uu____4878 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4878 in
              let uu____4879 =
                let uu____4880 =
                  let uu____4881 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4881 in
                FStar_SMTEncoding_Term.unboxInt uu____4880 in
              (uu____4877, uu____4879) in
            let mk_default uu____4887 =
              let uu____4888 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4888 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4939 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4939
              then
                let uu____4940 = let uu____4941 = mk_args ts in op uu____4941 in
                FStar_All.pipe_right uu____4940 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4970 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4970
              then
                let uu____4971 = binary ts in
                match uu____4971 with
                | (t1,t2) ->
                    let uu____4978 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4978
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4982 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4982
                 then
                   let uu____4983 = op (binary ts) in
                   FStar_All.pipe_right uu____4983
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
            let uu____5114 =
              let uu____5123 =
                FStar_List.tryFind
                  (fun uu____5145  ->
                     match uu____5145 with
                     | (l,uu____5155) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5123 FStar_Util.must in
            (match uu____5114 with
             | (uu____5194,op) ->
                 let uu____5204 = op arg_tms in (uu____5204, decls))
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
        let uu____5212 = FStar_List.hd args_e in
        match uu____5212 with
        | (tm_sz,uu____5220) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5230 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5230 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5238 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5238);
                   t_decls) in
            let uu____5239 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5259::(sz_arg,uu____5261)::uu____5262::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5311 =
                    let uu____5314 = FStar_List.tail args_e in
                    FStar_List.tail uu____5314 in
                  let uu____5317 =
                    let uu____5320 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5320 in
                  (uu____5311, uu____5317)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5326::(sz_arg,uu____5328)::uu____5329::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5378 =
                    let uu____5379 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5379 in
                  failwith uu____5378
              | uu____5388 ->
                  let uu____5395 = FStar_List.tail args_e in
                  (uu____5395, FStar_Pervasives_Native.None) in
            (match uu____5239 with
             | (arg_tms,ext_sz) ->
                 let uu____5418 = encode_args arg_tms env in
                 (match uu____5418 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5439 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5448 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5448 in
                      let unary_arith arg_tms2 =
                        let uu____5457 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5457 in
                      let binary arg_tms2 =
                        let uu____5470 =
                          let uu____5471 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5471 in
                        let uu____5472 =
                          let uu____5473 =
                            let uu____5474 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5474 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5473 in
                        (uu____5470, uu____5472) in
                      let binary_arith arg_tms2 =
                        let uu____5489 =
                          let uu____5490 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5490 in
                        let uu____5491 =
                          let uu____5492 =
                            let uu____5493 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5493 in
                          FStar_SMTEncoding_Term.unboxInt uu____5492 in
                        (uu____5489, uu____5491) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5542 =
                          let uu____5543 = mk_args ts in op uu____5543 in
                        FStar_All.pipe_right uu____5542 resBox in
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
                        let uu____5651 =
                          let uu____5654 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5654 in
                        let uu____5656 =
                          let uu____5659 =
                            let uu____5660 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5660 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5659 in
                        mk_bv uu____5651 unary uu____5656 arg_tms2 in
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
                      let uu____5859 =
                        let uu____5868 =
                          FStar_List.tryFind
                            (fun uu____5890  ->
                               match uu____5890 with
                               | (l,uu____5900) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5868 FStar_Util.must in
                      (match uu____5859 with
                       | (uu____5941,op) ->
                           let uu____5951 = op arg_tms1 in
                           (uu____5951, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5962 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5962
       then
         let uu____5963 = FStar_Syntax_Print.tag_of_term t in
         let uu____5964 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5965 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5963 uu____5964
           uu____5965
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5971 ->
           let uu____5996 =
             let uu____5997 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5998 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5999 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6000 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5997
               uu____5998 uu____5999 uu____6000 in
           failwith uu____5996
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6005 =
             let uu____6006 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6007 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6008 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6009 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6006
               uu____6007 uu____6008 uu____6009 in
           failwith uu____6005
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6015 =
             let uu____6016 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6016 in
           failwith uu____6015
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6023) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6064;
              FStar_Syntax_Syntax.vars = uu____6065;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6082 = varops.fresh "t" in
             (uu____6082, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6085 =
               let uu____6096 =
                 let uu____6099 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6099 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6096) in
             FStar_SMTEncoding_Term.DeclFun uu____6085 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6107) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6117 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6117, [])
       | FStar_Syntax_Syntax.Tm_type uu____6120 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6124) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6149 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6149 with
            | (binders1,res) ->
                let uu____6160 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6160
                then
                  let uu____6165 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6165 with
                   | (vars,guards,env',decls,uu____6190) ->
                       let fsym =
                         let uu____6208 = varops.fresh "f" in
                         (uu____6208, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6211 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___396_6220 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___396_6220.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___396_6220.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___396_6220.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___396_6220.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___396_6220.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___396_6220.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___396_6220.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___396_6220.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___396_6220.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___396_6220.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___396_6220.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___396_6220.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___396_6220.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___396_6220.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___396_6220.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___396_6220.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___396_6220.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___396_6220.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___396_6220.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___396_6220.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___396_6220.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___396_6220.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___396_6220.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___396_6220.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___396_6220.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___396_6220.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___396_6220.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___396_6220.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___396_6220.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___396_6220.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___396_6220.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___396_6220.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___396_6220.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6211 with
                        | (pre_opt,res_t) ->
                            let uu____6231 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6231 with
                             | (res_pred,decls') ->
                                 let uu____6242 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6255 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6255, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6259 =
                                         encode_formula pre env' in
                                       (match uu____6259 with
                                        | (guard,decls0) ->
                                            let uu____6272 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6272, decls0)) in
                                 (match uu____6242 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6284 =
                                          let uu____6295 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6295) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6284 in
                                      let cvars =
                                        let uu____6313 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6313
                                          (FStar_List.filter
                                             (fun uu____6327  ->
                                                match uu____6327 with
                                                | (x,uu____6333) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6352 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6352 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6360 =
                                             let uu____6361 =
                                               let uu____6368 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6368) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6361 in
                                           (uu____6360,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6388 =
                                               let uu____6389 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6389 in
                                             varops.mk_unique uu____6388 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6400 =
                                               FStar_Options.log_queries () in
                                             if uu____6400
                                             then
                                               let uu____6403 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6403
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6411 =
                                               let uu____6418 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6418) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6411 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6430 =
                                               let uu____6437 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6437,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6430 in
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
                                             let uu____6458 =
                                               let uu____6465 =
                                                 let uu____6466 =
                                                   let uu____6477 =
                                                     let uu____6478 =
                                                       let uu____6483 =
                                                         let uu____6484 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6484 in
                                                       (f_has_t, uu____6483) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6478 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6477) in
                                                 mkForall_fuel uu____6466 in
                                               (uu____6465,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6458 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6507 =
                                               let uu____6514 =
                                                 let uu____6515 =
                                                   let uu____6526 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6526) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6515 in
                                               (uu____6514,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6507 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6551 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6551);
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
                     let uu____6566 =
                       let uu____6573 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6573,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6566 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6585 =
                       let uu____6592 =
                         let uu____6593 =
                           let uu____6604 =
                             let uu____6605 =
                               let uu____6610 =
                                 let uu____6611 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6611 in
                               (f_has_t, uu____6610) in
                             FStar_SMTEncoding_Util.mkImp uu____6605 in
                           ([[f_has_t]], [fsym], uu____6604) in
                         mkForall_fuel uu____6593 in
                       (uu____6592, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6585 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6638 ->
           let uu____6645 =
             let uu____6650 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6650 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6657;
                 FStar_Syntax_Syntax.vars = uu____6658;_} ->
                 let uu____6665 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6665 with
                  | (b,f1) ->
                      let uu____6690 =
                        let uu____6691 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6691 in
                      (uu____6690, f1))
             | uu____6700 -> failwith "impossible" in
           (match uu____6645 with
            | (x,f) ->
                let uu____6711 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6711 with
                 | (base_t,decls) ->
                     let uu____6722 = gen_term_var env x in
                     (match uu____6722 with
                      | (x1,xtm,env') ->
                          let uu____6736 = encode_formula f env' in
                          (match uu____6736 with
                           | (refinement,decls') ->
                               let uu____6747 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6747 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6763 =
                                        let uu____6766 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6773 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6766
                                          uu____6773 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6763 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6806  ->
                                              match uu____6806 with
                                              | (y,uu____6812) ->
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
                                    let uu____6845 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6845 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6853 =
                                           let uu____6854 =
                                             let uu____6861 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6861) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6854 in
                                         (uu____6853,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6882 =
                                             let uu____6883 =
                                               let uu____6884 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6884 in
                                             Prims.strcat module_name
                                               uu____6883 in
                                           varops.mk_unique uu____6882 in
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
                                           let uu____6898 =
                                             let uu____6905 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6905) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6898 in
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
                                           let uu____6920 =
                                             let uu____6927 =
                                               let uu____6928 =
                                                 let uu____6939 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6939) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6928 in
                                             (uu____6927,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6920 in
                                         let t_kinding =
                                           let uu____6957 =
                                             let uu____6964 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6964,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6957 in
                                         let t_interp =
                                           let uu____6982 =
                                             let uu____6989 =
                                               let uu____6990 =
                                                 let uu____7001 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7001) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6990 in
                                             let uu____7024 =
                                               let uu____7027 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7027 in
                                             (uu____6989, uu____7024,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6982 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7034 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7034);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7064 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7064 in
           let uu____7065 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7065 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7077 =
                    let uu____7084 =
                      let uu____7085 =
                        let uu____7086 =
                          let uu____7087 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7087 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7086 in
                      varops.mk_unique uu____7085 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7084) in
                  FStar_SMTEncoding_Util.mkAssume uu____7077 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7092 ->
           let uu____7107 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7107 with
            | (head1,args_e) ->
                let uu____7148 =
                  let uu____7161 =
                    let uu____7162 = FStar_Syntax_Subst.compress head1 in
                    uu____7162.FStar_Syntax_Syntax.n in
                  (uu____7161, args_e) in
                (match uu____7148 with
                 | uu____7177 when head_redex env head1 ->
                     let uu____7190 = whnf env t in
                     encode_term uu____7190 env
                 | uu____7191 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7210 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7224;
                       FStar_Syntax_Syntax.vars = uu____7225;_},uu____7226),uu____7227::
                    (v1,uu____7229)::(v2,uu____7231)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7282 = encode_term v1 env in
                     (match uu____7282 with
                      | (v11,decls1) ->
                          let uu____7293 = encode_term v2 env in
                          (match uu____7293 with
                           | (v21,decls2) ->
                               let uu____7304 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7304,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7308::(v1,uu____7310)::(v2,uu____7312)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7359 = encode_term v1 env in
                     (match uu____7359 with
                      | (v11,decls1) ->
                          let uu____7370 = encode_term v2 env in
                          (match uu____7370 with
                           | (v21,decls2) ->
                               let uu____7381 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7381,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7385)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7411)::(arg,uu____7413)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7448) ->
                     let e0 =
                       let uu____7466 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7466 in
                     ((let uu____7474 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7474
                       then
                         let uu____7475 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7475
                       else ());
                      (let e =
                         let uu____7480 =
                           let uu____7481 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7482 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7481
                             uu____7482 in
                         uu____7480 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7491),(arg,uu____7493)::[]) -> encode_term arg env
                 | uu____7518 ->
                     let uu____7531 = encode_args args_e env in
                     (match uu____7531 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7586 = encode_term head1 env in
                            match uu____7586 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7650 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7650 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7728  ->
                                                 fun uu____7729  ->
                                                   match (uu____7728,
                                                           uu____7729)
                                                   with
                                                   | ((bv,uu____7751),
                                                      (a,uu____7753)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7771 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7771
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7776 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7776 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7791 =
                                                   let uu____7798 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7807 =
                                                     let uu____7808 =
                                                       let uu____7809 =
                                                         let uu____7810 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7810 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7809 in
                                                     varops.mk_unique
                                                       uu____7808 in
                                                   (uu____7798,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7807) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7791 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7827 = lookup_free_var_sym env fv in
                            match uu____7827 with
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
                                   FStar_Syntax_Syntax.pos = uu____7858;
                                   FStar_Syntax_Syntax.vars = uu____7859;_},uu____7860)
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
                                   FStar_Syntax_Syntax.pos = uu____7871;
                                   FStar_Syntax_Syntax.vars = uu____7872;_},uu____7873)
                                ->
                                let uu____7878 =
                                  let uu____7879 =
                                    let uu____7884 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7884
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7879
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7878
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7914 =
                                  let uu____7915 =
                                    let uu____7920 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7920
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7915
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7914
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7949,(FStar_Util.Inl t1,uu____7951),uu____7952)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8001,(FStar_Util.Inr c,uu____8003),uu____8004)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8053 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8080 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8080 in
                               let uu____8081 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8081 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8097;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8098;_},uu____8099)
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
                                     | uu____8113 ->
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
           let uu____8162 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8162 with
            | (bs1,body1,opening) ->
                let fallback uu____8185 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8192 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8192, [decl]) in
                let is_impure rc =
                  let uu____8199 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8199 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8209 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8209
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8229 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8229
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8233 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8233)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8240 =
                         let uu____8245 =
                           let uu____8246 =
                             FStar_Syntax_Print.term_to_string t0 in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8246 in
                         (FStar_Errors.FunctionLiteralPrecisionLoss,
                           uu____8245) in
                       FStar_Errors.maybe_fatal_error
                         t0.FStar_Syntax_Syntax.pos uu____8240);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8248 =
                       (is_impure rc) &&
                         (let uu____8250 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8250) in
                     if uu____8248
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8257 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8257 with
                        | (vars,guards,envbody,decls,uu____8282) ->
                            let body2 =
                              let uu____8296 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8296
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8298 = encode_term body2 envbody in
                            (match uu____8298 with
                             | (body3,decls') ->
                                 let uu____8309 =
                                   let uu____8318 = codomain_eff rc in
                                   match uu____8318 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8337 = encode_term tfun env in
                                       (match uu____8337 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8309 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8369 =
                                          let uu____8380 =
                                            let uu____8381 =
                                              let uu____8386 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8386, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8381 in
                                          ([], vars, uu____8380) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8369 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8398 =
                                              let uu____8401 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8401
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8398 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8420 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8420 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8428 =
                                             let uu____8429 =
                                               let uu____8436 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8436) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8429 in
                                           (uu____8428,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8447 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8447 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8458 =
                                                    let uu____8459 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8459 = cache_size in
                                                  if uu____8458
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
                                                    let uu____8475 =
                                                      let uu____8476 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8476 in
                                                    varops.mk_unique
                                                      uu____8475 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8483 =
                                                    let uu____8490 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8490) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8483 in
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
                                                      let uu____8508 =
                                                        let uu____8509 =
                                                          let uu____8516 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8516,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8509 in
                                                      [uu____8508] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8529 =
                                                    let uu____8536 =
                                                      let uu____8537 =
                                                        let uu____8548 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8548) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8537 in
                                                    (uu____8536,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8529 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8565 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8565);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8568,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8569;
                          FStar_Syntax_Syntax.lbunivs = uu____8570;
                          FStar_Syntax_Syntax.lbtyp = uu____8571;
                          FStar_Syntax_Syntax.lbeff = uu____8572;
                          FStar_Syntax_Syntax.lbdef = uu____8573;_}::uu____8574),uu____8575)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8601;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8603;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8624 ->
           (FStar_Errors.diag t.FStar_Syntax_Syntax.pos
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
              let uu____8694 = encode_term e1 env in
              match uu____8694 with
              | (ee1,decls1) ->
                  let uu____8705 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8705 with
                   | (xs,e21) ->
                       let uu____8730 = FStar_List.hd xs in
                       (match uu____8730 with
                        | (x1,uu____8744) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8746 = encode_body e21 env' in
                            (match uu____8746 with
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
            let uu____8778 =
              let uu____8785 =
                let uu____8786 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8786 in
              gen_term_var env uu____8785 in
            match uu____8778 with
            | (scrsym,scr',env1) ->
                let uu____8794 = encode_term e env1 in
                (match uu____8794 with
                 | (scr,decls) ->
                     let uu____8805 =
                       let encode_branch b uu____8830 =
                         match uu____8830 with
                         | (else_case,decls1) ->
                             let uu____8849 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8849 with
                              | (p,w,br) ->
                                  let uu____8875 = encode_pat env1 p in
                                  (match uu____8875 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8912  ->
                                                   match uu____8912 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8919 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8941 =
                                               encode_term w1 env2 in
                                             (match uu____8941 with
                                              | (w2,decls2) ->
                                                  let uu____8954 =
                                                    let uu____8955 =
                                                      let uu____8960 =
                                                        let uu____8961 =
                                                          let uu____8966 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8966) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8961 in
                                                      (guard, uu____8960) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8955 in
                                                  (uu____8954, decls2)) in
                                       (match uu____8919 with
                                        | (guard1,decls2) ->
                                            let uu____8979 =
                                              encode_br br env2 in
                                            (match uu____8979 with
                                             | (br1,decls3) ->
                                                 let uu____8992 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8992,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8805 with
                      | (match_tm,decls1) ->
                          let uu____9011 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9011, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9051 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9051
       then
         let uu____9052 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9052
       else ());
      (let uu____9054 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9054 with
       | (vars,pat_term) ->
           let uu____9071 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9124  ->
                     fun v1  ->
                       match uu____9124 with
                       | (env1,vars1) ->
                           let uu____9176 = gen_term_var env1 v1 in
                           (match uu____9176 with
                            | (xx,uu____9198,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9071 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9277 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9278 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9279 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9287 = encode_const c env1 in
                      (match uu____9287 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9301::uu____9302 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9305 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9328 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9328 with
                        | (uu____9335,uu____9336::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9339 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9372  ->
                                  match uu____9372 with
                                  | (arg,uu____9380) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9386 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9386)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9413) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9444 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9467 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9511  ->
                                  match uu____9511 with
                                  | (arg,uu____9525) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9531 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9531)) in
                      FStar_All.pipe_right uu____9467 FStar_List.flatten in
                let pat_term1 uu____9559 = encode_term pat_term env1 in
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
      let uu____9569 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9607  ->
                fun uu____9608  ->
                  match (uu____9607, uu____9608) with
                  | ((tms,decls),(t,uu____9644)) ->
                      let uu____9665 = encode_term t env in
                      (match uu____9665 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9569 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9722 = FStar_Syntax_Util.list_elements e in
        match uu____9722 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.maybe_fatal_error e.FStar_Syntax_Syntax.pos
               (FStar_Errors.NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____9743 =
          let uu____9758 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9758 FStar_Syntax_Util.head_and_args in
        match uu____9743 with
        | (head1,args) ->
            let uu____9797 =
              let uu____9810 =
                let uu____9811 = FStar_Syntax_Util.un_uinst head1 in
                uu____9811.FStar_Syntax_Syntax.n in
              (uu____9810, args) in
            (match uu____9797 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9825,uu____9826)::(e,uu____9828)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9863 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9899 =
            let uu____9914 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9914 FStar_Syntax_Util.head_and_args in
          match uu____9899 with
          | (head1,args) ->
              let uu____9955 =
                let uu____9968 =
                  let uu____9969 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9969.FStar_Syntax_Syntax.n in
                (uu____9968, args) in
              (match uu____9955 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9986)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10013 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10035 = smt_pat_or1 t1 in
            (match uu____10035 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10051 = list_elements1 e in
                 FStar_All.pipe_right uu____10051
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10069 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10069
                           (FStar_List.map one_pat)))
             | uu____10080 ->
                 let uu____10085 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10085])
        | uu____10106 ->
            let uu____10109 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10109] in
      let uu____10130 =
        let uu____10149 =
          let uu____10150 = FStar_Syntax_Subst.compress t in
          uu____10150.FStar_Syntax_Syntax.n in
        match uu____10149 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10189 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10189 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10232;
                        FStar_Syntax_Syntax.effect_name = uu____10233;
                        FStar_Syntax_Syntax.result_typ = uu____10234;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10236)::(post,uu____10238)::(pats,uu____10240)::[];
                        FStar_Syntax_Syntax.flags = uu____10241;_}
                      ->
                      let uu____10282 = lemma_pats pats in
                      (binders1, pre, post, uu____10282)
                  | uu____10299 -> failwith "impos"))
        | uu____10318 -> failwith "Impos" in
      match uu____10130 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___397_10366 = env in
            {
              bindings = (uu___397_10366.bindings);
              depth = (uu___397_10366.depth);
              tcenv = (uu___397_10366.tcenv);
              warn = (uu___397_10366.warn);
              cache = (uu___397_10366.cache);
              nolabels = (uu___397_10366.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___397_10366.encode_non_total_function_typ);
              current_module_name = (uu___397_10366.current_module_name)
            } in
          let uu____10367 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10367 with
           | (vars,guards,env2,decls,uu____10392) ->
               let uu____10405 =
                 let uu____10418 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10462 =
                             let uu____10471 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10471
                               FStar_List.unzip in
                           match uu____10462 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10418 FStar_List.unzip in
               (match uu____10405 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___398_10583 = env2 in
                      {
                        bindings = (uu___398_10583.bindings);
                        depth = (uu___398_10583.depth);
                        tcenv = (uu___398_10583.tcenv);
                        warn = (uu___398_10583.warn);
                        cache = (uu___398_10583.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___398_10583.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___398_10583.encode_non_total_function_typ);
                        current_module_name =
                          (uu___398_10583.current_module_name)
                      } in
                    let uu____10584 =
                      let uu____10589 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10589 env3 in
                    (match uu____10584 with
                     | (pre1,decls'') ->
                         let uu____10596 =
                           let uu____10601 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10601 env3 in
                         (match uu____10596 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10611 =
                                let uu____10612 =
                                  let uu____10623 =
                                    let uu____10624 =
                                      let uu____10629 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10629, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10624 in
                                  (pats, vars, uu____10623) in
                                FStar_SMTEncoding_Util.mkForall uu____10612 in
                              (uu____10611, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10648 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10648
        then
          let uu____10649 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10650 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10649 uu____10650
        else () in
      let enc f r l =
        let uu____10683 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10711 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10711 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10683 with
        | (decls,args) ->
            let uu____10740 =
              let uu___399_10741 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___399_10741.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___399_10741.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10740, decls) in
      let const_op f r uu____10772 =
        let uu____10785 = f r in (uu____10785, []) in
      let un_op f l =
        let uu____10804 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10804 in
      let bin_op f uu___373_10820 =
        match uu___373_10820 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10831 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10865 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10888  ->
                 match uu____10888 with
                 | (t,uu____10902) ->
                     let uu____10903 = encode_formula t env in
                     (match uu____10903 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10865 with
        | (decls,phis) ->
            let uu____10932 =
              let uu___400_10933 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___400_10933.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___400_10933.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10932, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10994  ->
               match uu____10994 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11013) -> false
                    | uu____11014 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11029 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11029
        else
          (let uu____11043 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11043 r rf) in
      let mk_imp1 r uu___374_11068 =
        match uu___374_11068 with
        | (lhs,uu____11074)::(rhs,uu____11076)::[] ->
            let uu____11103 = encode_formula rhs env in
            (match uu____11103 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11118) ->
                      (l1, decls1)
                  | uu____11123 ->
                      let uu____11124 = encode_formula lhs env in
                      (match uu____11124 with
                       | (l2,decls2) ->
                           let uu____11135 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11135, (FStar_List.append decls1 decls2)))))
        | uu____11138 -> failwith "impossible" in
      let mk_ite r uu___375_11159 =
        match uu___375_11159 with
        | (guard,uu____11165)::(_then,uu____11167)::(_else,uu____11169)::[]
            ->
            let uu____11206 = encode_formula guard env in
            (match uu____11206 with
             | (g,decls1) ->
                 let uu____11217 = encode_formula _then env in
                 (match uu____11217 with
                  | (t,decls2) ->
                      let uu____11228 = encode_formula _else env in
                      (match uu____11228 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11242 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11267 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11267 in
      let connectives =
        let uu____11285 =
          let uu____11298 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11298) in
        let uu____11315 =
          let uu____11330 =
            let uu____11343 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11343) in
          let uu____11360 =
            let uu____11375 =
              let uu____11390 =
                let uu____11403 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11403) in
              let uu____11420 =
                let uu____11435 =
                  let uu____11450 =
                    let uu____11463 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11463) in
                  [uu____11450;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11435 in
              uu____11390 :: uu____11420 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11375 in
          uu____11330 :: uu____11360 in
        uu____11285 :: uu____11315 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11784 = encode_formula phi' env in
            (match uu____11784 with
             | (phi2,decls) ->
                 let uu____11795 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11795, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11796 ->
            let uu____11803 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11803 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11842 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11842 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11854;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11856;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11877 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11877 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11924::(x,uu____11926)::(t,uu____11928)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11975 = encode_term x env in
                 (match uu____11975 with
                  | (x1,decls) ->
                      let uu____11986 = encode_term t env in
                      (match uu____11986 with
                       | (t1,decls') ->
                           let uu____11997 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11997, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12002)::(msg,uu____12004)::(phi2,uu____12006)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12051 =
                   let uu____12056 =
                     let uu____12057 = FStar_Syntax_Subst.compress r in
                     uu____12057.FStar_Syntax_Syntax.n in
                   let uu____12060 =
                     let uu____12061 = FStar_Syntax_Subst.compress msg in
                     uu____12061.FStar_Syntax_Syntax.n in
                   (uu____12056, uu____12060) in
                 (match uu____12051 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12070))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12076 -> fallback phi2)
             | uu____12081 when head_redex env head2 ->
                 let uu____12094 = whnf env phi1 in
                 encode_formula uu____12094 env
             | uu____12095 ->
                 let uu____12108 = encode_term phi1 env in
                 (match uu____12108 with
                  | (tt,decls) ->
                      let uu____12119 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___401_12122 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___401_12122.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___401_12122.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12119, decls)))
        | uu____12123 ->
            let uu____12124 = encode_term phi1 env in
            (match uu____12124 with
             | (tt,decls) ->
                 let uu____12135 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___402_12138 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___402_12138.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___402_12138.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12135, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12174 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12174 with
        | (vars,guards,env2,decls,uu____12213) ->
            let uu____12226 =
              let uu____12239 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12287 =
                          let uu____12296 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12326  ->
                                    match uu____12326 with
                                    | (t,uu____12336) ->
                                        encode_term t
                                          (let uu___403_12338 = env2 in
                                           {
                                             bindings =
                                               (uu___403_12338.bindings);
                                             depth = (uu___403_12338.depth);
                                             tcenv = (uu___403_12338.tcenv);
                                             warn = (uu___403_12338.warn);
                                             cache = (uu___403_12338.cache);
                                             nolabels =
                                               (uu___403_12338.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___403_12338.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___403_12338.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12296 FStar_List.unzip in
                        match uu____12287 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12239 FStar_List.unzip in
            (match uu____12226 with
             | (pats,decls') ->
                 let uu____12437 = encode_formula body env2 in
                 (match uu____12437 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12469;
                             FStar_SMTEncoding_Term.rng = uu____12470;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12485 -> guards in
                      let uu____12490 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12490, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12550  ->
                   match uu____12550 with
                   | (x,uu____12556) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12564 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12576 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12576) uu____12564 tl1 in
             let uu____12579 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12606  ->
                       match uu____12606 with
                       | (b,uu____12612) ->
                           let uu____12613 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12613)) in
             (match uu____12579 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12619) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12633 =
                    let uu____12638 =
                      let uu____12639 = FStar_Syntax_Print.bv_to_string x in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12639 in
                    (FStar_Errors.SMTPatternMissingBoundVar, uu____12638) in
                  FStar_Errors.maybe_fatal_error pos uu____12633) in
       let uu____12640 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12640 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12649 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12707  ->
                     match uu____12707 with
                     | (l,uu____12721) -> FStar_Ident.lid_equals op l)) in
           (match uu____12649 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12754,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12794 = encode_q_body env vars pats body in
             match uu____12794 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12839 =
                     let uu____12850 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12850) in
                   FStar_SMTEncoding_Term.mkForall uu____12839
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12869 = encode_q_body env vars pats body in
             match uu____12869 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12913 =
                   let uu____12914 =
                     let uu____12925 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12925) in
                   FStar_SMTEncoding_Term.mkExists uu____12914
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12913, decls))))
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
  let uu____13018 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13018 with
  | (asym,a) ->
      let uu____13025 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13025 with
       | (xsym,x) ->
           let uu____13032 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13032 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13076 =
                      let uu____13087 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13087, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13076 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13113 =
                      let uu____13120 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13120) in
                    FStar_SMTEncoding_Util.mkApp uu____13113 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13133 =
                    let uu____13136 =
                      let uu____13139 =
                        let uu____13142 =
                          let uu____13143 =
                            let uu____13150 =
                              let uu____13151 =
                                let uu____13162 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13162) in
                              FStar_SMTEncoding_Util.mkForall uu____13151 in
                            (uu____13150, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13143 in
                        let uu____13179 =
                          let uu____13182 =
                            let uu____13183 =
                              let uu____13190 =
                                let uu____13191 =
                                  let uu____13202 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13202) in
                                FStar_SMTEncoding_Util.mkForall uu____13191 in
                              (uu____13190,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13183 in
                          [uu____13182] in
                        uu____13142 :: uu____13179 in
                      xtok_decl :: uu____13139 in
                    xname_decl :: uu____13136 in
                  (xtok1, uu____13133) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13293 =
                    let uu____13306 =
                      let uu____13315 =
                        let uu____13316 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13316 in
                      quant axy uu____13315 in
                    (FStar_Parser_Const.op_Eq, uu____13306) in
                  let uu____13325 =
                    let uu____13340 =
                      let uu____13353 =
                        let uu____13362 =
                          let uu____13363 =
                            let uu____13364 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13364 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13363 in
                        quant axy uu____13362 in
                      (FStar_Parser_Const.op_notEq, uu____13353) in
                    let uu____13373 =
                      let uu____13388 =
                        let uu____13401 =
                          let uu____13410 =
                            let uu____13411 =
                              let uu____13412 =
                                let uu____13417 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13418 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13417, uu____13418) in
                              FStar_SMTEncoding_Util.mkLT uu____13412 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13411 in
                          quant xy uu____13410 in
                        (FStar_Parser_Const.op_LT, uu____13401) in
                      let uu____13427 =
                        let uu____13442 =
                          let uu____13455 =
                            let uu____13464 =
                              let uu____13465 =
                                let uu____13466 =
                                  let uu____13471 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13472 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13471, uu____13472) in
                                FStar_SMTEncoding_Util.mkLTE uu____13466 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13465 in
                            quant xy uu____13464 in
                          (FStar_Parser_Const.op_LTE, uu____13455) in
                        let uu____13481 =
                          let uu____13496 =
                            let uu____13509 =
                              let uu____13518 =
                                let uu____13519 =
                                  let uu____13520 =
                                    let uu____13525 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13526 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13525, uu____13526) in
                                  FStar_SMTEncoding_Util.mkGT uu____13520 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13519 in
                              quant xy uu____13518 in
                            (FStar_Parser_Const.op_GT, uu____13509) in
                          let uu____13535 =
                            let uu____13550 =
                              let uu____13563 =
                                let uu____13572 =
                                  let uu____13573 =
                                    let uu____13574 =
                                      let uu____13579 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13580 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13579, uu____13580) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13574 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13573 in
                                quant xy uu____13572 in
                              (FStar_Parser_Const.op_GTE, uu____13563) in
                            let uu____13589 =
                              let uu____13604 =
                                let uu____13617 =
                                  let uu____13626 =
                                    let uu____13627 =
                                      let uu____13628 =
                                        let uu____13633 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13634 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13633, uu____13634) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13628 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13627 in
                                  quant xy uu____13626 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13617) in
                              let uu____13643 =
                                let uu____13658 =
                                  let uu____13671 =
                                    let uu____13680 =
                                      let uu____13681 =
                                        let uu____13682 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13682 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13681 in
                                    quant qx uu____13680 in
                                  (FStar_Parser_Const.op_Minus, uu____13671) in
                                let uu____13691 =
                                  let uu____13706 =
                                    let uu____13719 =
                                      let uu____13728 =
                                        let uu____13729 =
                                          let uu____13730 =
                                            let uu____13735 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13736 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13735, uu____13736) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13730 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13729 in
                                      quant xy uu____13728 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13719) in
                                  let uu____13745 =
                                    let uu____13760 =
                                      let uu____13773 =
                                        let uu____13782 =
                                          let uu____13783 =
                                            let uu____13784 =
                                              let uu____13789 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13790 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13789, uu____13790) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13784 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13783 in
                                        quant xy uu____13782 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13773) in
                                    let uu____13799 =
                                      let uu____13814 =
                                        let uu____13827 =
                                          let uu____13836 =
                                            let uu____13837 =
                                              let uu____13838 =
                                                let uu____13843 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13844 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13843, uu____13844) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13838 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13837 in
                                          quant xy uu____13836 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13827) in
                                      let uu____13853 =
                                        let uu____13868 =
                                          let uu____13881 =
                                            let uu____13890 =
                                              let uu____13891 =
                                                let uu____13892 =
                                                  let uu____13897 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13898 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13897, uu____13898) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13892 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13891 in
                                            quant xy uu____13890 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13881) in
                                        let uu____13907 =
                                          let uu____13922 =
                                            let uu____13935 =
                                              let uu____13944 =
                                                let uu____13945 =
                                                  let uu____13946 =
                                                    let uu____13951 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13952 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13951,
                                                      uu____13952) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13946 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13945 in
                                              quant xy uu____13944 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13935) in
                                          let uu____13961 =
                                            let uu____13976 =
                                              let uu____13989 =
                                                let uu____13998 =
                                                  let uu____13999 =
                                                    let uu____14000 =
                                                      let uu____14005 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14006 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14005,
                                                        uu____14006) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14000 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13999 in
                                                quant xy uu____13998 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13989) in
                                            let uu____14015 =
                                              let uu____14030 =
                                                let uu____14043 =
                                                  let uu____14052 =
                                                    let uu____14053 =
                                                      let uu____14054 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14054 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14053 in
                                                  quant qx uu____14052 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14043) in
                                              [uu____14030] in
                                            uu____13976 :: uu____14015 in
                                          uu____13922 :: uu____13961 in
                                        uu____13868 :: uu____13907 in
                                      uu____13814 :: uu____13853 in
                                    uu____13760 :: uu____13799 in
                                  uu____13706 :: uu____13745 in
                                uu____13658 :: uu____13691 in
                              uu____13604 :: uu____13643 in
                            uu____13550 :: uu____13589 in
                          uu____13496 :: uu____13535 in
                        uu____13442 :: uu____13481 in
                      uu____13388 :: uu____13427 in
                    uu____13340 :: uu____13373 in
                  uu____13293 :: uu____13325 in
                let mk1 l v1 =
                  let uu____14268 =
                    let uu____14277 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14335  ->
                              match uu____14335 with
                              | (l',uu____14349) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14277
                      (FStar_Option.map
                         (fun uu____14409  ->
                            match uu____14409 with | (uu____14428,b) -> b v1)) in
                  FStar_All.pipe_right uu____14268 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14499  ->
                          match uu____14499 with
                          | (l',uu____14513) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14551 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14551 with
        | (xxsym,xx) ->
            let uu____14558 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14558 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14568 =
                   let uu____14575 =
                     let uu____14576 =
                       let uu____14587 =
                         let uu____14588 =
                           let uu____14593 =
                             let uu____14594 =
                               let uu____14599 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14599) in
                             FStar_SMTEncoding_Util.mkEq uu____14594 in
                           (xx_has_type, uu____14593) in
                         FStar_SMTEncoding_Util.mkImp uu____14588 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14587) in
                     FStar_SMTEncoding_Util.mkForall uu____14576 in
                   let uu____14624 =
                     let uu____14625 =
                       let uu____14626 =
                         let uu____14627 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14627 in
                       Prims.strcat module_name uu____14626 in
                     varops.mk_unique uu____14625 in
                   (uu____14575, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14624) in
                 FStar_SMTEncoding_Util.mkAssume uu____14568)
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
    let uu____14663 =
      let uu____14664 =
        let uu____14671 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14671, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14664 in
    let uu____14674 =
      let uu____14677 =
        let uu____14678 =
          let uu____14685 =
            let uu____14686 =
              let uu____14697 =
                let uu____14698 =
                  let uu____14703 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14703) in
                FStar_SMTEncoding_Util.mkImp uu____14698 in
              ([[typing_pred]], [xx], uu____14697) in
            mkForall_fuel uu____14686 in
          (uu____14685, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14678 in
      [uu____14677] in
    uu____14663 :: uu____14674 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14745 =
      let uu____14746 =
        let uu____14753 =
          let uu____14754 =
            let uu____14765 =
              let uu____14770 =
                let uu____14773 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14773] in
              [uu____14770] in
            let uu____14778 =
              let uu____14779 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14779 tt in
            (uu____14765, [bb], uu____14778) in
          FStar_SMTEncoding_Util.mkForall uu____14754 in
        (uu____14753, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14746 in
    let uu____14800 =
      let uu____14803 =
        let uu____14804 =
          let uu____14811 =
            let uu____14812 =
              let uu____14823 =
                let uu____14824 =
                  let uu____14829 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14829) in
                FStar_SMTEncoding_Util.mkImp uu____14824 in
              ([[typing_pred]], [xx], uu____14823) in
            mkForall_fuel uu____14812 in
          (uu____14811, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14804 in
      [uu____14803] in
    uu____14745 :: uu____14800 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14879 =
        let uu____14880 =
          let uu____14887 =
            let uu____14890 =
              let uu____14893 =
                let uu____14896 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14897 =
                  let uu____14900 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14900] in
                uu____14896 :: uu____14897 in
              tt :: uu____14893 in
            tt :: uu____14890 in
          ("Prims.Precedes", uu____14887) in
        FStar_SMTEncoding_Util.mkApp uu____14880 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14879 in
    let precedes_y_x =
      let uu____14904 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14904 in
    let uu____14907 =
      let uu____14908 =
        let uu____14915 =
          let uu____14916 =
            let uu____14927 =
              let uu____14932 =
                let uu____14935 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14935] in
              [uu____14932] in
            let uu____14940 =
              let uu____14941 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14941 tt in
            (uu____14927, [bb], uu____14940) in
          FStar_SMTEncoding_Util.mkForall uu____14916 in
        (uu____14915, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14908 in
    let uu____14962 =
      let uu____14965 =
        let uu____14966 =
          let uu____14973 =
            let uu____14974 =
              let uu____14985 =
                let uu____14986 =
                  let uu____14991 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14991) in
                FStar_SMTEncoding_Util.mkImp uu____14986 in
              ([[typing_pred]], [xx], uu____14985) in
            mkForall_fuel uu____14974 in
          (uu____14973, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14966 in
      let uu____15016 =
        let uu____15019 =
          let uu____15020 =
            let uu____15027 =
              let uu____15028 =
                let uu____15039 =
                  let uu____15040 =
                    let uu____15045 =
                      let uu____15046 =
                        let uu____15049 =
                          let uu____15052 =
                            let uu____15055 =
                              let uu____15056 =
                                let uu____15061 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15062 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15061, uu____15062) in
                              FStar_SMTEncoding_Util.mkGT uu____15056 in
                            let uu____15063 =
                              let uu____15066 =
                                let uu____15067 =
                                  let uu____15072 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15073 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15072, uu____15073) in
                                FStar_SMTEncoding_Util.mkGTE uu____15067 in
                              let uu____15074 =
                                let uu____15077 =
                                  let uu____15078 =
                                    let uu____15083 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15084 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15083, uu____15084) in
                                  FStar_SMTEncoding_Util.mkLT uu____15078 in
                                [uu____15077] in
                              uu____15066 :: uu____15074 in
                            uu____15055 :: uu____15063 in
                          typing_pred_y :: uu____15052 in
                        typing_pred :: uu____15049 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15046 in
                    (uu____15045, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15040 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15039) in
              mkForall_fuel uu____15028 in
            (uu____15027,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15020 in
        [uu____15019] in
      uu____14965 :: uu____15016 in
    uu____14907 :: uu____14962 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15130 =
      let uu____15131 =
        let uu____15138 =
          let uu____15139 =
            let uu____15150 =
              let uu____15155 =
                let uu____15158 = FStar_SMTEncoding_Term.boxString b in
                [uu____15158] in
              [uu____15155] in
            let uu____15163 =
              let uu____15164 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15164 tt in
            (uu____15150, [bb], uu____15163) in
          FStar_SMTEncoding_Util.mkForall uu____15139 in
        (uu____15138, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15131 in
    let uu____15185 =
      let uu____15188 =
        let uu____15189 =
          let uu____15196 =
            let uu____15197 =
              let uu____15208 =
                let uu____15209 =
                  let uu____15214 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15214) in
                FStar_SMTEncoding_Util.mkImp uu____15209 in
              ([[typing_pred]], [xx], uu____15208) in
            mkForall_fuel uu____15197 in
          (uu____15196, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15189 in
      [uu____15188] in
    uu____15130 :: uu____15185 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15267 =
      let uu____15268 =
        let uu____15275 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15275, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15268 in
    [uu____15267] in
  let mk_and_interp env conj uu____15287 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15312 =
      let uu____15313 =
        let uu____15320 =
          let uu____15321 =
            let uu____15332 =
              let uu____15333 =
                let uu____15338 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15338, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15333 in
            ([[l_and_a_b]], [aa; bb], uu____15332) in
          FStar_SMTEncoding_Util.mkForall uu____15321 in
        (uu____15320, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15313 in
    [uu____15312] in
  let mk_or_interp env disj uu____15376 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15401 =
      let uu____15402 =
        let uu____15409 =
          let uu____15410 =
            let uu____15421 =
              let uu____15422 =
                let uu____15427 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15427, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15422 in
            ([[l_or_a_b]], [aa; bb], uu____15421) in
          FStar_SMTEncoding_Util.mkForall uu____15410 in
        (uu____15409, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15402 in
    [uu____15401] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15490 =
      let uu____15491 =
        let uu____15498 =
          let uu____15499 =
            let uu____15510 =
              let uu____15511 =
                let uu____15516 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15516, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15511 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15510) in
          FStar_SMTEncoding_Util.mkForall uu____15499 in
        (uu____15498, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15491 in
    [uu____15490] in
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
    let uu____15589 =
      let uu____15590 =
        let uu____15597 =
          let uu____15598 =
            let uu____15609 =
              let uu____15610 =
                let uu____15615 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15615, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15610 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15609) in
          FStar_SMTEncoding_Util.mkForall uu____15598 in
        (uu____15597, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15590 in
    [uu____15589] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15686 =
      let uu____15687 =
        let uu____15694 =
          let uu____15695 =
            let uu____15706 =
              let uu____15707 =
                let uu____15712 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15712, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15707 in
            ([[l_imp_a_b]], [aa; bb], uu____15706) in
          FStar_SMTEncoding_Util.mkForall uu____15695 in
        (uu____15694, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15687 in
    [uu____15686] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15775 =
      let uu____15776 =
        let uu____15783 =
          let uu____15784 =
            let uu____15795 =
              let uu____15796 =
                let uu____15801 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15801, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15796 in
            ([[l_iff_a_b]], [aa; bb], uu____15795) in
          FStar_SMTEncoding_Util.mkForall uu____15784 in
        (uu____15783, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15776 in
    [uu____15775] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15853 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15853 in
    let uu____15856 =
      let uu____15857 =
        let uu____15864 =
          let uu____15865 =
            let uu____15876 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15876) in
          FStar_SMTEncoding_Util.mkForall uu____15865 in
        (uu____15864, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15857 in
    [uu____15856] in
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
      let uu____15936 =
        let uu____15943 =
          let uu____15946 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15946] in
        ("Valid", uu____15943) in
      FStar_SMTEncoding_Util.mkApp uu____15936 in
    let uu____15949 =
      let uu____15950 =
        let uu____15957 =
          let uu____15958 =
            let uu____15969 =
              let uu____15970 =
                let uu____15975 =
                  let uu____15976 =
                    let uu____15987 =
                      let uu____15992 =
                        let uu____15995 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15995] in
                      [uu____15992] in
                    let uu____16000 =
                      let uu____16001 =
                        let uu____16006 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16006, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16001 in
                    (uu____15987, [xx1], uu____16000) in
                  FStar_SMTEncoding_Util.mkForall uu____15976 in
                (uu____15975, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15970 in
            ([[l_forall_a_b]], [aa; bb], uu____15969) in
          FStar_SMTEncoding_Util.mkForall uu____15958 in
        (uu____15957, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15950 in
    [uu____15949] in
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
      let uu____16088 =
        let uu____16095 =
          let uu____16098 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16098] in
        ("Valid", uu____16095) in
      FStar_SMTEncoding_Util.mkApp uu____16088 in
    let uu____16101 =
      let uu____16102 =
        let uu____16109 =
          let uu____16110 =
            let uu____16121 =
              let uu____16122 =
                let uu____16127 =
                  let uu____16128 =
                    let uu____16139 =
                      let uu____16144 =
                        let uu____16147 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16147] in
                      [uu____16144] in
                    let uu____16152 =
                      let uu____16153 =
                        let uu____16158 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16158, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16153 in
                    (uu____16139, [xx1], uu____16152) in
                  FStar_SMTEncoding_Util.mkExists uu____16128 in
                (uu____16127, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16122 in
            ([[l_exists_a_b]], [aa; bb], uu____16121) in
          FStar_SMTEncoding_Util.mkForall uu____16110 in
        (uu____16109, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16102 in
    [uu____16101] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16218 =
      let uu____16219 =
        let uu____16226 =
          let uu____16227 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16227 range_ty in
        let uu____16228 = varops.mk_unique "typing_range_const" in
        (uu____16226, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16228) in
      FStar_SMTEncoding_Util.mkAssume uu____16219 in
    [uu____16218] in
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
        let uu____16262 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16262 x1 t in
      let uu____16263 =
        let uu____16274 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16274) in
      FStar_SMTEncoding_Util.mkForall uu____16263 in
    let uu____16297 =
      let uu____16298 =
        let uu____16305 =
          let uu____16306 =
            let uu____16317 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16317) in
          FStar_SMTEncoding_Util.mkForall uu____16306 in
        (uu____16305,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16298 in
    [uu____16297] in
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
          let uu____16641 =
            FStar_Util.find_opt
              (fun uu____16667  ->
                 match uu____16667 with
                 | (l,uu____16679) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16641 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16704,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16740 = encode_function_type_as_formula t env in
        match uu____16740 with
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
              let uu____16780 =
                ((let uu____16783 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16783) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16780
              then
                let uu____16790 = new_term_constant_and_tok_from_lid env lid in
                match uu____16790 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16809 =
                        let uu____16810 = FStar_Syntax_Subst.compress t_norm in
                        uu____16810.FStar_Syntax_Syntax.n in
                      match uu____16809 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16816) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16846  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16851 -> [] in
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
                (let uu____16865 = prims.is lid in
                 if uu____16865
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16873 = prims.mk lid vname in
                   match uu____16873 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16897 =
                      let uu____16908 = curried_arrow_formals_comp t_norm in
                      match uu____16908 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16926 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16926
                            then
                              let uu____16927 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___404_16930 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___404_16930.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___404_16930.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___404_16930.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___404_16930.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___404_16930.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___404_16930.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___404_16930.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___404_16930.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___404_16930.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___404_16930.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___404_16930.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___404_16930.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___404_16930.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___404_16930.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___404_16930.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___404_16930.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___404_16930.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___404_16930.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___404_16930.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___404_16930.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___404_16930.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___404_16930.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___404_16930.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___404_16930.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___404_16930.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___404_16930.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___404_16930.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___404_16930.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___404_16930.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___404_16930.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___404_16930.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___404_16930.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___404_16930.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16927
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16942 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16942)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16897 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16987 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16987 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17008 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___376_17050  ->
                                       match uu___376_17050 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17054 =
                                             FStar_Util.prefix vars in
                                           (match uu____17054 with
                                            | (uu____17075,(xxsym,uu____17077))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17095 =
                                                  let uu____17096 =
                                                    let uu____17103 =
                                                      let uu____17104 =
                                                        let uu____17115 =
                                                          let uu____17116 =
                                                            let uu____17121 =
                                                              let uu____17122
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17122 in
                                                            (vapp,
                                                              uu____17121) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17116 in
                                                        ([[vapp]], vars,
                                                          uu____17115) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17104 in
                                                    (uu____17103,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17096 in
                                                [uu____17095])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17141 =
                                             FStar_Util.prefix vars in
                                           (match uu____17141 with
                                            | (uu____17162,(xxsym,uu____17164))
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
                                                let uu____17187 =
                                                  let uu____17188 =
                                                    let uu____17195 =
                                                      let uu____17196 =
                                                        let uu____17207 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17207) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17196 in
                                                    (uu____17195,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17188 in
                                                [uu____17187])
                                       | uu____17224 -> [])) in
                             let uu____17225 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17225 with
                              | (vars,guards,env',decls1,uu____17252) ->
                                  let uu____17265 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17274 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17274, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17276 =
                                          encode_formula p env' in
                                        (match uu____17276 with
                                         | (g,ds) ->
                                             let uu____17287 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17287,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17265 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17300 =
                                           let uu____17307 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17307) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17300 in
                                       let uu____17316 =
                                         let vname_decl =
                                           let uu____17324 =
                                             let uu____17335 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17345  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17335,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17324 in
                                         let uu____17354 =
                                           let env2 =
                                             let uu___405_17360 = env1 in
                                             {
                                               bindings =
                                                 (uu___405_17360.bindings);
                                               depth = (uu___405_17360.depth);
                                               tcenv = (uu___405_17360.tcenv);
                                               warn = (uu___405_17360.warn);
                                               cache = (uu___405_17360.cache);
                                               nolabels =
                                                 (uu___405_17360.nolabels);
                                               use_zfuel_name =
                                                 (uu___405_17360.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___405_17360.current_module_name)
                                             } in
                                           let uu____17361 =
                                             let uu____17362 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17362 in
                                           if uu____17361
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17354 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17377::uu____17378 ->
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
                                                     let uu____17418 =
                                                       let uu____17429 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17429) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17418 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17456 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17459 =
                                               match formals with
                                               | [] ->
                                                   let uu____17476 =
                                                     let uu____17477 =
                                                       let uu____17480 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17480 in
                                                     push_free_var env1 lid
                                                       vname uu____17477 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17476)
                                               | uu____17485 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17492 =
                                                       let uu____17499 =
                                                         let uu____17500 =
                                                           let uu____17511 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17511) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17500 in
                                                       (uu____17499,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17492 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17459 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17316 with
                                        | (decls2,env2) ->
                                            let uu____17554 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17562 =
                                                encode_term res_t1 env' in
                                              match uu____17562 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17575 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17575, decls) in
                                            (match uu____17554 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17586 =
                                                     let uu____17593 =
                                                       let uu____17594 =
                                                         let uu____17605 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17605) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17594 in
                                                     (uu____17593,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17586 in
                                                 let freshness =
                                                   let uu____17621 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17621
                                                   then
                                                     let uu____17626 =
                                                       let uu____17627 =
                                                         let uu____17638 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17649 =
                                                           varops.next_id () in
                                                         (vname, uu____17638,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17649) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17627 in
                                                     let uu____17652 =
                                                       let uu____17655 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17655] in
                                                     uu____17626 ::
                                                       uu____17652
                                                   else [] in
                                                 let g =
                                                   let uu____17660 =
                                                     let uu____17663 =
                                                       let uu____17666 =
                                                         let uu____17669 =
                                                           let uu____17672 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17672 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17669 in
                                                       FStar_List.append
                                                         decls3 uu____17666 in
                                                     FStar_List.append decls2
                                                       uu____17663 in
                                                   FStar_List.append decls11
                                                     uu____17660 in
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
          let uu____17703 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17703 with
          | FStar_Pervasives_Native.None  ->
              let uu____17740 = encode_free_var false env x t t_norm [] in
              (match uu____17740 with
               | (decls,env1) ->
                   let uu____17767 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17767 with
                    | (n1,x',uu____17794) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17815) ->
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
            let uu____17870 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17870 with
            | (decls,env1) ->
                let uu____17889 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17889
                then
                  let uu____17896 =
                    let uu____17899 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17899 in
                  (uu____17896, env1)
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
             (fun uu____17951  ->
                fun lb  ->
                  match uu____17951 with
                  | (decls,env1) ->
                      let uu____17971 =
                        let uu____17978 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17978
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17971 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____17999 = FStar_Syntax_Util.head_and_args t in
    match uu____17999 with
    | (hd1,args) ->
        let uu____18036 =
          let uu____18037 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18037.FStar_Syntax_Syntax.n in
        (match uu____18036 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18041,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18060 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18082  ->
      fun quals  ->
        match uu____18082 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18158 = FStar_Util.first_N nbinders formals in
              match uu____18158 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18239  ->
                         fun uu____18240  ->
                           match (uu____18239, uu____18240) with
                           | ((formal,uu____18258),(binder,uu____18260)) ->
                               let uu____18269 =
                                 let uu____18276 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18276) in
                               FStar_Syntax_Syntax.NT uu____18269) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18284 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18315  ->
                              match uu____18315 with
                              | (x,i) ->
                                  let uu____18326 =
                                    let uu___406_18327 = x in
                                    let uu____18328 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___406_18327.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___406_18327.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18328
                                    } in
                                  (uu____18326, i))) in
                    FStar_All.pipe_right uu____18284
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18346 =
                      let uu____18347 = FStar_Syntax_Subst.compress body in
                      let uu____18348 =
                        let uu____18349 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18349 in
                      FStar_Syntax_Syntax.extend_app_n uu____18347
                        uu____18348 in
                    uu____18346 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18410 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18410
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___407_18413 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___407_18413.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___407_18413.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___407_18413.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___407_18413.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___407_18413.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___407_18413.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___407_18413.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___407_18413.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___407_18413.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___407_18413.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___407_18413.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___407_18413.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___407_18413.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___407_18413.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___407_18413.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___407_18413.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___407_18413.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___407_18413.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___407_18413.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___407_18413.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___407_18413.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___407_18413.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___407_18413.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___407_18413.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___407_18413.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___407_18413.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___407_18413.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___407_18413.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___407_18413.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___407_18413.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___407_18413.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___407_18413.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___407_18413.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18446 = FStar_Syntax_Util.abs_formals e in
                match uu____18446 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18510::uu____18511 ->
                         let uu____18526 =
                           let uu____18527 =
                             let uu____18530 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18530 in
                           uu____18527.FStar_Syntax_Syntax.n in
                         (match uu____18526 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18573 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18573 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18615 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18615
                                   then
                                     let uu____18650 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18650 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18744  ->
                                                   fun uu____18745  ->
                                                     match (uu____18744,
                                                             uu____18745)
                                                     with
                                                     | ((x,uu____18763),
                                                        (b,uu____18765)) ->
                                                         let uu____18774 =
                                                           let uu____18781 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18781) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18774)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18783 =
                                            let uu____18804 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18804) in
                                          (uu____18783, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18872 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18872 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18961) ->
                              let uu____18966 =
                                let uu____18987 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18987 in
                              (uu____18966, true)
                          | uu____19052 when Prims.op_Negation norm1 ->
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
                          | uu____19054 ->
                              let uu____19055 =
                                let uu____19056 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19057 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19056
                                  uu____19057 in
                              failwith uu____19055)
                     | uu____19082 ->
                         let rec aux' t_norm2 =
                           let uu____19107 =
                             let uu____19108 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19108.FStar_Syntax_Syntax.n in
                           match uu____19107 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19149 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19149 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19177 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19177 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19257)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19262 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19318 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19318
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19330 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19424  ->
                            fun lb  ->
                              match uu____19424 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19519 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19519
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19522 =
                                      let uu____19537 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19537
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19522 with
                                    | (tok,decl,env2) ->
                                        let uu____19583 =
                                          let uu____19596 =
                                            let uu____19607 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19607, tok) in
                                          uu____19596 :: toks in
                                        (uu____19583, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19330 with
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
                        | uu____19790 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19798 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19798 vars)
                            else
                              (let uu____19800 =
                                 let uu____19807 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19807) in
                               FStar_SMTEncoding_Util.mkApp uu____19800) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19889;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19891;
                             FStar_Syntax_Syntax.lbeff = uu____19892;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19955 =
                              let uu____19962 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19962 with
                              | (tcenv',uu____19980,e_t) ->
                                  let uu____19986 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19997 -> failwith "Impossible" in
                                  (match uu____19986 with
                                   | (e1,t_norm1) ->
                                       ((let uu___410_20013 = env2 in
                                         {
                                           bindings =
                                             (uu___410_20013.bindings);
                                           depth = (uu___410_20013.depth);
                                           tcenv = tcenv';
                                           warn = (uu___410_20013.warn);
                                           cache = (uu___410_20013.cache);
                                           nolabels =
                                             (uu___410_20013.nolabels);
                                           use_zfuel_name =
                                             (uu___410_20013.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___410_20013.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___410_20013.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19955 with
                             | (env',e1,t_norm1) ->
                                 let uu____20023 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20023 with
                                  | ((binders,body,uu____20044,uu____20045),curry)
                                      ->
                                      ((let uu____20056 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20056
                                        then
                                          let uu____20057 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20058 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20057 uu____20058
                                        else ());
                                       (let uu____20060 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20060 with
                                        | (vars,guards,env'1,binder_decls,uu____20087)
                                            ->
                                            let body1 =
                                              let uu____20101 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20101
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20104 =
                                              let uu____20113 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20113
                                              then
                                                let uu____20124 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20125 =
                                                  encode_formula body1 env'1 in
                                                (uu____20124, uu____20125)
                                              else
                                                (let uu____20135 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20135)) in
                                            (match uu____20104 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20158 =
                                                     let uu____20165 =
                                                       let uu____20166 =
                                                         let uu____20177 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20177) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20166 in
                                                     let uu____20188 =
                                                       let uu____20191 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20191 in
                                                     (uu____20165,
                                                       uu____20188,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20158 in
                                                 let uu____20194 =
                                                   let uu____20197 =
                                                     let uu____20200 =
                                                       let uu____20203 =
                                                         let uu____20206 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20206 in
                                                       FStar_List.append
                                                         decls2 uu____20203 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20200 in
                                                   FStar_List.append decls1
                                                     uu____20197 in
                                                 (uu____20194, env2))))))
                        | uu____20211 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20296 = varops.fresh "fuel" in
                          (uu____20296, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20299 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20387  ->
                                  fun uu____20388  ->
                                    match (uu____20387, uu____20388) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20536 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20536 in
                                        let gtok =
                                          let uu____20538 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20538 in
                                        let env4 =
                                          let uu____20540 =
                                            let uu____20543 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20543 in
                                          push_free_var env3 flid gtok
                                            uu____20540 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20299 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20699 t_norm
                              uu____20701 =
                              match (uu____20699, uu____20701) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20745;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20746;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20774 =
                                    let uu____20781 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20781 with
                                    | (tcenv',uu____20803,e_t) ->
                                        let uu____20809 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20820 ->
                                              failwith "Impossible" in
                                        (match uu____20809 with
                                         | (e1,t_norm1) ->
                                             ((let uu___411_20836 = env3 in
                                               {
                                                 bindings =
                                                   (uu___411_20836.bindings);
                                                 depth =
                                                   (uu___411_20836.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___411_20836.warn);
                                                 cache =
                                                   (uu___411_20836.cache);
                                                 nolabels =
                                                   (uu___411_20836.nolabels);
                                                 use_zfuel_name =
                                                   (uu___411_20836.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___411_20836.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___411_20836.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20774 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20851 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20851
                                         then
                                           let uu____20852 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20853 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20854 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20852 uu____20853
                                             uu____20854
                                         else ());
                                        (let uu____20856 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20856 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20893 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20893
                                               then
                                                 let uu____20894 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20895 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20896 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20897 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20894 uu____20895
                                                   uu____20896 uu____20897
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20901 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20901 with
                                               | (vars,guards,env'1,binder_decls,uu____20932)
                                                   ->
                                                   let decl_g =
                                                     let uu____20946 =
                                                       let uu____20957 =
                                                         let uu____20960 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20960 in
                                                       (g, uu____20957,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20946 in
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
                                                     let uu____20985 =
                                                       let uu____20992 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20992) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20985 in
                                                   let gsapp =
                                                     let uu____21002 =
                                                       let uu____21009 =
                                                         let uu____21012 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21012 ::
                                                           vars_tm in
                                                       (g, uu____21009) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21002 in
                                                   let gmax =
                                                     let uu____21018 =
                                                       let uu____21025 =
                                                         let uu____21028 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21028 ::
                                                           vars_tm in
                                                       (g, uu____21025) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21018 in
                                                   let body1 =
                                                     let uu____21034 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21034
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21036 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21036 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21054 =
                                                            let uu____21061 =
                                                              let uu____21062
                                                                =
                                                                let uu____21077
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
                                                                  uu____21077) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21062 in
                                                            let uu____21098 =
                                                              let uu____21101
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21101 in
                                                            (uu____21061,
                                                              uu____21098,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21054 in
                                                        let eqn_f =
                                                          let uu____21105 =
                                                            let uu____21112 =
                                                              let uu____21113
                                                                =
                                                                let uu____21124
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21124) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21113 in
                                                            (uu____21112,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21105 in
                                                        let eqn_g' =
                                                          let uu____21138 =
                                                            let uu____21145 =
                                                              let uu____21146
                                                                =
                                                                let uu____21157
                                                                  =
                                                                  let uu____21158
                                                                    =
                                                                    let uu____21163
                                                                    =
                                                                    let uu____21164
                                                                    =
                                                                    let uu____21171
                                                                    =
                                                                    let uu____21174
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21174
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21171) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21164 in
                                                                    (gsapp,
                                                                    uu____21163) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21158 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21157) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21146 in
                                                            (uu____21145,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21138 in
                                                        let uu____21197 =
                                                          let uu____21206 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21206
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21235)
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
                                                                  let uu____21260
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21260
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21265
                                                                  =
                                                                  let uu____21272
                                                                    =
                                                                    let uu____21273
                                                                    =
                                                                    let uu____21284
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21284) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21273 in
                                                                  (uu____21272,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21265 in
                                                              let uu____21305
                                                                =
                                                                let uu____21312
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21312
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21325
                                                                    =
                                                                    let uu____21328
                                                                    =
                                                                    let uu____21329
                                                                    =
                                                                    let uu____21336
                                                                    =
                                                                    let uu____21337
                                                                    =
                                                                    let uu____21348
                                                                    =
                                                                    let uu____21349
                                                                    =
                                                                    let uu____21354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21354,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21349 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21348) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21337 in
                                                                    (uu____21336,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21329 in
                                                                    [uu____21328] in
                                                                    (d3,
                                                                    uu____21325) in
                                                              (match uu____21305
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21197
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
                            let uu____21419 =
                              let uu____21432 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21511  ->
                                   fun uu____21512  ->
                                     match (uu____21511, uu____21512) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21667 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21667 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21432 in
                            (match uu____21419 with
                             | (decls2,eqns,env01) ->
                                 let uu____21740 =
                                   let isDeclFun uu___377_21752 =
                                     match uu___377_21752 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21753 -> true
                                     | uu____21764 -> false in
                                   let uu____21765 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21765
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21740 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21805 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___378_21809  ->
                                 match uu___378_21809 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21810 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21816 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21816))) in
                      if uu____21805
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
                   let uu____21868 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21868
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
        let uu____21917 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21917 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21921 = encode_sigelt' env se in
      match uu____21921 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21937 =
                  let uu____21938 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21938 in
                [uu____21937]
            | uu____21939 ->
                let uu____21940 =
                  let uu____21943 =
                    let uu____21944 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21944 in
                  uu____21943 :: g in
                let uu____21945 =
                  let uu____21948 =
                    let uu____21949 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21949 in
                  [uu____21948] in
                FStar_List.append uu____21940 uu____21945 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21962 =
          let uu____21963 = FStar_Syntax_Subst.compress t in
          uu____21963.FStar_Syntax_Syntax.n in
        match uu____21962 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21967)) -> s = "opaque_to_smt"
        | uu____21968 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21973 =
          let uu____21974 = FStar_Syntax_Subst.compress t in
          uu____21974.FStar_Syntax_Syntax.n in
        match uu____21973 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21978)) -> s = "uninterpreted_by_smt"
        | uu____21979 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21984 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21989 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21992 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21995 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22010 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22014 =
            let uu____22015 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22015 Prims.op_Negation in
          if uu____22014
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22041 ->
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
               let uu____22061 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22061 with
               | (aname,atok,env2) ->
                   let uu____22077 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22077 with
                    | (formals,uu____22095) ->
                        let uu____22108 =
                          let uu____22113 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22113 env2 in
                        (match uu____22108 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22125 =
                                 let uu____22126 =
                                   let uu____22137 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22153  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22137,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22126 in
                               [uu____22125;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22166 =
                               let aux uu____22218 uu____22219 =
                                 match (uu____22218, uu____22219) with
                                 | ((bv,uu____22271),(env3,acc_sorts,acc)) ->
                                     let uu____22309 = gen_term_var env3 bv in
                                     (match uu____22309 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22166 with
                              | (uu____22381,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22404 =
                                      let uu____22411 =
                                        let uu____22412 =
                                          let uu____22423 =
                                            let uu____22424 =
                                              let uu____22429 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22429) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22424 in
                                          ([[app]], xs_sorts, uu____22423) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22412 in
                                      (uu____22411,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22404 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22449 =
                                      let uu____22456 =
                                        let uu____22457 =
                                          let uu____22468 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22468) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22457 in
                                      (uu____22456,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22449 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22487 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22487 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22515,uu____22516)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22517 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22517 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22534,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22540 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___379_22544  ->
                      match uu___379_22544 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22545 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22550 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22551 -> false)) in
            Prims.op_Negation uu____22540 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22560 =
               let uu____22567 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22567 env fv t quals in
             match uu____22560 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22582 =
                   let uu____22585 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22585 in
                 (uu____22582, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22593 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22593 with
           | (uu____22602,f1) ->
               let uu____22604 = encode_formula f1 env in
               (match uu____22604 with
                | (f2,decls) ->
                    let g =
                      let uu____22618 =
                        let uu____22619 =
                          let uu____22626 =
                            let uu____22629 =
                              let uu____22630 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22630 in
                            FStar_Pervasives_Native.Some uu____22629 in
                          let uu____22631 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22626, uu____22631) in
                        FStar_SMTEncoding_Util.mkAssume uu____22619 in
                      [uu____22618] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22637) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22649 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22667 =
                       let uu____22670 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22670.FStar_Syntax_Syntax.fv_name in
                     uu____22667.FStar_Syntax_Syntax.v in
                   let uu____22671 =
                     let uu____22672 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22672 in
                   if uu____22671
                   then
                     let val_decl =
                       let uu___414_22700 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___414_22700.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___414_22700.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___414_22700.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22705 = encode_sigelt' env1 val_decl in
                     match uu____22705 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22649 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22733,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22735;
                          FStar_Syntax_Syntax.lbtyp = uu____22736;
                          FStar_Syntax_Syntax.lbeff = uu____22737;
                          FStar_Syntax_Syntax.lbdef = uu____22738;_}::[]),uu____22739)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22758 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22758 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22787 =
                   let uu____22790 =
                     let uu____22791 =
                       let uu____22798 =
                         let uu____22799 =
                           let uu____22810 =
                             let uu____22811 =
                               let uu____22816 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22816) in
                             FStar_SMTEncoding_Util.mkEq uu____22811 in
                           ([[b2t_x]], [xx], uu____22810) in
                         FStar_SMTEncoding_Util.mkForall uu____22799 in
                       (uu____22798,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22791 in
                   [uu____22790] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22787 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22849,uu____22850) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___380_22859  ->
                  match uu___380_22859 with
                  | FStar_Syntax_Syntax.Discriminator uu____22860 -> true
                  | uu____22861 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22864,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22875 =
                     let uu____22876 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22876.FStar_Ident.idText in
                   uu____22875 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___381_22880  ->
                     match uu___381_22880 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22881 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22885) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___382_22902  ->
                  match uu___382_22902 with
                  | FStar_Syntax_Syntax.Projector uu____22903 -> true
                  | uu____22908 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22911 = try_lookup_free_var env l in
          (match uu____22911 with
           | FStar_Pervasives_Native.Some uu____22918 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___415_22922 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___415_22922.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___415_22922.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___415_22922.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22929) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22947) ->
          let uu____22956 = encode_sigelts env ses in
          (match uu____22956 with
           | (g,env1) ->
               let uu____22973 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___383_22996  ->
                         match uu___383_22996 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22997;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22998;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22999;_}
                             -> false
                         | uu____23002 -> true)) in
               (match uu____22973 with
                | (g',inversions) ->
                    let uu____23017 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___384_23038  ->
                              match uu___384_23038 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23039 ->
                                  true
                              | uu____23050 -> false)) in
                    (match uu____23017 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23068,tps,k,uu____23071,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___385_23088  ->
                    match uu___385_23088 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23089 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23098 = c in
              match uu____23098 with
              | (name,args,uu____23103,uu____23104,uu____23105) ->
                  let uu____23110 =
                    let uu____23111 =
                      let uu____23122 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23139  ->
                                match uu____23139 with
                                | (uu____23146,sort,uu____23148) -> sort)) in
                      (name, uu____23122, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23111 in
                  [uu____23110]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23175 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23181 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23181 FStar_Option.isNone)) in
            if uu____23175
            then []
            else
              (let uu____23213 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23213 with
               | (xxsym,xx) ->
                   let uu____23222 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23261  ->
                             fun l  ->
                               match uu____23261 with
                               | (out,decls) ->
                                   let uu____23281 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23281 with
                                    | (uu____23292,data_t) ->
                                        let uu____23294 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23294 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23340 =
                                                 let uu____23341 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23341.FStar_Syntax_Syntax.n in
                                               match uu____23340 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23352,indices) ->
                                                   indices
                                               | uu____23374 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23398  ->
                                                         match uu____23398
                                                         with
                                                         | (x,uu____23404) ->
                                                             let uu____23405
                                                               =
                                                               let uu____23406
                                                                 =
                                                                 let uu____23413
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23413,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23406 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23405)
                                                    env) in
                                             let uu____23416 =
                                               encode_args indices env1 in
                                             (match uu____23416 with
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
                                                      let uu____23442 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23458
                                                                 =
                                                                 let uu____23463
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23463,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23458)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23442
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23466 =
                                                      let uu____23467 =
                                                        let uu____23472 =
                                                          let uu____23473 =
                                                            let uu____23478 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23478,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23473 in
                                                        (out, uu____23472) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23467 in
                                                    (uu____23466,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23222 with
                    | (data_ax,decls) ->
                        let uu____23491 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23491 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23502 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23502 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23506 =
                                 let uu____23513 =
                                   let uu____23514 =
                                     let uu____23525 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23540 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23525,
                                       uu____23540) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23514 in
                                 let uu____23555 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23513,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23555) in
                               FStar_SMTEncoding_Util.mkAssume uu____23506 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23558 =
            let uu____23571 =
              let uu____23572 = FStar_Syntax_Subst.compress k in
              uu____23572.FStar_Syntax_Syntax.n in
            match uu____23571 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23617 -> (tps, k) in
          (match uu____23558 with
           | (formals,res) ->
               let uu____23640 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23640 with
                | (formals1,res1) ->
                    let uu____23651 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23651 with
                     | (vars,guards,env',binder_decls,uu____23676) ->
                         let uu____23689 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23689 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23708 =
                                  let uu____23715 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23715) in
                                FStar_SMTEncoding_Util.mkApp uu____23708 in
                              let uu____23724 =
                                let tname_decl =
                                  let uu____23734 =
                                    let uu____23735 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23767  ->
                                              match uu____23767 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23780 = varops.next_id () in
                                    (tname, uu____23735,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23780, false) in
                                  constructor_or_logic_type_decl uu____23734 in
                                let uu____23789 =
                                  match vars with
                                  | [] ->
                                      let uu____23802 =
                                        let uu____23803 =
                                          let uu____23806 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23806 in
                                        push_free_var env1 t tname
                                          uu____23803 in
                                      ([], uu____23802)
                                  | uu____23813 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23822 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23822 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23836 =
                                          let uu____23843 =
                                            let uu____23844 =
                                              let uu____23859 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23859) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23844 in
                                          (uu____23843,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23836 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23789 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23724 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23899 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23899 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23917 =
                                               let uu____23918 =
                                                 let uu____23925 =
                                                   let uu____23926 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23926 in
                                                 (uu____23925,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23918 in
                                             [uu____23917]
                                           else [] in
                                         let uu____23930 =
                                           let uu____23933 =
                                             let uu____23936 =
                                               let uu____23937 =
                                                 let uu____23944 =
                                                   let uu____23945 =
                                                     let uu____23956 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23956) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23945 in
                                                 (uu____23944,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23937 in
                                             [uu____23936] in
                                           FStar_List.append karr uu____23933 in
                                         FStar_List.append decls1 uu____23930 in
                                   let aux =
                                     let uu____23972 =
                                       let uu____23975 =
                                         inversion_axioms tapp vars in
                                       let uu____23978 =
                                         let uu____23981 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23981] in
                                       FStar_List.append uu____23975
                                         uu____23978 in
                                     FStar_List.append kindingAx uu____23972 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23988,uu____23989,uu____23990,uu____23991,uu____23992)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24000,t,uu____24002,n_tps,uu____24004) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24012 = new_term_constant_and_tok_from_lid env d in
          (match uu____24012 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24029 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24029 with
                | (formals,t_res) ->
                    let uu____24064 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24064 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24078 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24078 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24148 =
                                            mk_term_projector_name d x in
                                          (uu____24148,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24150 =
                                  let uu____24169 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24169, true) in
                                FStar_All.pipe_right uu____24150
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
                              let uu____24208 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24208 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24220::uu____24221 ->
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
                                         let uu____24266 =
                                           let uu____24277 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24277) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24266
                                     | uu____24302 -> tok_typing in
                                   let uu____24311 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24311 with
                                    | (vars',guards',env'',decls_formals,uu____24336)
                                        ->
                                        let uu____24349 =
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
                                        (match uu____24349 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24380 ->
                                                   let uu____24387 =
                                                     let uu____24388 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24388 in
                                                   [uu____24387] in
                                             let encode_elim uu____24398 =
                                               let uu____24399 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24399 with
                                               | (head1,args) ->
                                                   let uu____24442 =
                                                     let uu____24443 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24443.FStar_Syntax_Syntax.n in
                                                   (match uu____24442 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24453;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24454;_},uu____24455)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24461 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24461
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
                                                                 | uu____24504
                                                                    ->
                                                                    let uu____24505
                                                                    =
                                                                    let uu____24510
                                                                    =
                                                                    let uu____24511
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24511 in
                                                                    (FStar_Errors.NonVaribleInductiveTypeParameter,
                                                                    uu____24510) in
                                                                    FStar_Errors.raise_error
                                                                    uu____24505
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24527
                                                                    =
                                                                    let uu____24528
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24528 in
                                                                    if
                                                                    uu____24527
                                                                    then
                                                                    let uu____24541
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24541]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24543
                                                               =
                                                               let uu____24556
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24606
                                                                     ->
                                                                    fun
                                                                    uu____24607
                                                                     ->
                                                                    match 
                                                                    (uu____24606,
                                                                    uu____24607)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24702
                                                                    =
                                                                    let uu____24709
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24709 in
                                                                    (match uu____24702
                                                                    with
                                                                    | 
                                                                    (uu____24722,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24730
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24730
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24732
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24732
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
                                                                 uu____24556 in
                                                             (match uu____24543
                                                              with
                                                              | (uu____24747,arg_vars,elim_eqns_or_guards,uu____24750)
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
                                                                    let uu____24780
                                                                    =
                                                                    let uu____24787
                                                                    =
                                                                    let uu____24788
                                                                    =
                                                                    let uu____24799
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24810
                                                                    =
                                                                    let uu____24811
                                                                    =
                                                                    let uu____24816
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24816) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24811 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24799,
                                                                    uu____24810) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24788 in
                                                                    (uu____24787,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24780 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24839
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24839,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24841
                                                                    =
                                                                    let uu____24848
                                                                    =
                                                                    let uu____24849
                                                                    =
                                                                    let uu____24860
                                                                    =
                                                                    let uu____24865
                                                                    =
                                                                    let uu____24868
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24868] in
                                                                    [uu____24865] in
                                                                    let uu____24873
                                                                    =
                                                                    let uu____24874
                                                                    =
                                                                    let uu____24879
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24880
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24879,
                                                                    uu____24880) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24874 in
                                                                    (uu____24860,
                                                                    [x],
                                                                    uu____24873) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24849 in
                                                                    let uu____24899
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24848,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24899) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24841
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24906
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
                                                                    (let uu____24934
                                                                    =
                                                                    let uu____24935
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24935
                                                                    dapp1 in
                                                                    [uu____24934]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24906
                                                                    FStar_List.flatten in
                                                                    let uu____24942
                                                                    =
                                                                    let uu____24949
                                                                    =
                                                                    let uu____24950
                                                                    =
                                                                    let uu____24961
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24972
                                                                    =
                                                                    let uu____24973
                                                                    =
                                                                    let uu____24978
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24978) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24973 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24961,
                                                                    uu____24972) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24950 in
                                                                    (uu____24949,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24942) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24999 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24999
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
                                                                 | uu____25042
                                                                    ->
                                                                    let uu____25043
                                                                    =
                                                                    let uu____25048
                                                                    =
                                                                    let uu____25049
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25049 in
                                                                    (FStar_Errors.NonVaribleInductiveTypeParameter,
                                                                    uu____25048) in
                                                                    FStar_Errors.raise_error
                                                                    uu____25043
                                                                    orig_arg.FStar_Syntax_Syntax.pos in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25065
                                                                    =
                                                                    let uu____25066
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25066 in
                                                                    if
                                                                    uu____25065
                                                                    then
                                                                    let uu____25079
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25079]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25081
                                                               =
                                                               let uu____25094
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25144
                                                                     ->
                                                                    fun
                                                                    uu____25145
                                                                     ->
                                                                    match 
                                                                    (uu____25144,
                                                                    uu____25145)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25240
                                                                    =
                                                                    let uu____25247
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25247 in
                                                                    (match uu____25240
                                                                    with
                                                                    | 
                                                                    (uu____25260,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25268
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25268
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25270
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25270
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
                                                                 uu____25094 in
                                                             (match uu____25081
                                                              with
                                                              | (uu____25285,arg_vars,elim_eqns_or_guards,uu____25288)
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
                                                                    let uu____25318
                                                                    =
                                                                    let uu____25325
                                                                    =
                                                                    let uu____25326
                                                                    =
                                                                    let uu____25337
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25348
                                                                    =
                                                                    let uu____25349
                                                                    =
                                                                    let uu____25354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25354) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25349 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25337,
                                                                    uu____25348) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25326 in
                                                                    (uu____25325,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25318 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25377
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25377,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25379
                                                                    =
                                                                    let uu____25386
                                                                    =
                                                                    let uu____25387
                                                                    =
                                                                    let uu____25398
                                                                    =
                                                                    let uu____25403
                                                                    =
                                                                    let uu____25406
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25406] in
                                                                    [uu____25403] in
                                                                    let uu____25411
                                                                    =
                                                                    let uu____25412
                                                                    =
                                                                    let uu____25417
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25418
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25417,
                                                                    uu____25418) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25412 in
                                                                    (uu____25398,
                                                                    [x],
                                                                    uu____25411) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25387 in
                                                                    let uu____25437
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25386,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25437) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25379
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25444
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
                                                                    (let uu____25472
                                                                    =
                                                                    let uu____25473
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25473
                                                                    dapp1 in
                                                                    [uu____25472]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25444
                                                                    FStar_List.flatten in
                                                                    let uu____25480
                                                                    =
                                                                    let uu____25487
                                                                    =
                                                                    let uu____25488
                                                                    =
                                                                    let uu____25499
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25510
                                                                    =
                                                                    let uu____25511
                                                                    =
                                                                    let uu____25516
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25516) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25511 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25499,
                                                                    uu____25510) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25488 in
                                                                    (uu____25487,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25480) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25535 ->
                                                        ((let uu____25537 =
                                                            let uu____25542 =
                                                              let uu____25543
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d in
                                                              let uu____25544
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25543
                                                                uu____25544 in
                                                            (FStar_Errors.UnexpectedConstructorType,
                                                              uu____25542) in
                                                          FStar_Errors.maybe_fatal_error
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25537);
                                                         ([], []))) in
                                             let uu____25549 = encode_elim () in
                                             (match uu____25549 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25569 =
                                                      let uu____25572 =
                                                        let uu____25575 =
                                                          let uu____25578 =
                                                            let uu____25581 =
                                                              let uu____25582
                                                                =
                                                                let uu____25593
                                                                  =
                                                                  let uu____25596
                                                                    =
                                                                    let uu____25597
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25597 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25596 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25593) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25582 in
                                                            [uu____25581] in
                                                          let uu____25602 =
                                                            let uu____25605 =
                                                              let uu____25608
                                                                =
                                                                let uu____25611
                                                                  =
                                                                  let uu____25614
                                                                    =
                                                                    let uu____25617
                                                                    =
                                                                    let uu____25620
                                                                    =
                                                                    let uu____25621
                                                                    =
                                                                    let uu____25628
                                                                    =
                                                                    let uu____25629
                                                                    =
                                                                    let uu____25640
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25640) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25629 in
                                                                    (uu____25628,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25621 in
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25656
                                                                    =
                                                                    let uu____25657
                                                                    =
                                                                    let uu____25664
                                                                    =
                                                                    let uu____25665
                                                                    =
                                                                    let uu____25676
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25687
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25676,
                                                                    uu____25687) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25665 in
                                                                    (uu____25664,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25657 in
                                                                    [uu____25656] in
                                                                    uu____25620
                                                                    ::
                                                                    uu____25653 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25617 in
                                                                  FStar_List.append
                                                                    uu____25614
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25611 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25608 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25605 in
                                                          FStar_List.append
                                                            uu____25578
                                                            uu____25602 in
                                                        FStar_List.append
                                                          decls3 uu____25575 in
                                                      FStar_List.append
                                                        decls2 uu____25572 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25569 in
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
           (fun uu____25733  ->
              fun se  ->
                match uu____25733 with
                | (g,env1) ->
                    let uu____25753 = encode_sigelt env1 se in
                    (match uu____25753 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25810 =
        match uu____25810 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25842 ->
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
                 ((let uu____25848 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25848
                   then
                     let uu____25849 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25850 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25851 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25849 uu____25850 uu____25851
                   else ());
                  (let uu____25853 = encode_term t1 env1 in
                   match uu____25853 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25869 =
                         let uu____25876 =
                           let uu____25877 =
                             let uu____25878 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25878
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25877 in
                         new_term_constant_from_string env1 x uu____25876 in
                       (match uu____25869 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25894 = FStar_Options.log_queries () in
                              if uu____25894
                              then
                                let uu____25897 =
                                  let uu____25898 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25899 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25900 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25898 uu____25899 uu____25900 in
                                FStar_Pervasives_Native.Some uu____25897
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25916,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25930 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25930 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25953,se,uu____25955) ->
                 let uu____25960 = encode_sigelt env1 se in
                 (match uu____25960 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25977,se) ->
                 let uu____25983 = encode_sigelt env1 se in
                 (match uu____25983 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26000 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26000 with | (uu____26023,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26035 'Auu____26036 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26036,'Auu____26035)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26104  ->
              match uu____26104 with
              | (l,uu____26116,uu____26117) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26163  ->
              match uu____26163 with
              | (l,uu____26177,uu____26178) ->
                  let uu____26187 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26188 =
                    let uu____26191 =
                      let uu____26192 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26192 in
                    [uu____26191] in
                  uu____26187 :: uu____26188)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26213 =
      let uu____26216 =
        let uu____26217 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26220 =
          let uu____26221 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26221 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26217;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26220
        } in
      [uu____26216] in
    FStar_ST.op_Colon_Equals last_env uu____26213
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26278 = FStar_ST.op_Bang last_env in
      match uu____26278 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26332 ->
          let uu___416_26335 = e in
          let uu____26336 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___416_26335.bindings);
            depth = (uu___416_26335.depth);
            tcenv;
            warn = (uu___416_26335.warn);
            cache = (uu___416_26335.cache);
            nolabels = (uu___416_26335.nolabels);
            use_zfuel_name = (uu___416_26335.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___416_26335.encode_non_total_function_typ);
            current_module_name = uu____26336
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26340 = FStar_ST.op_Bang last_env in
    match uu____26340 with
    | [] -> failwith "Empty env stack"
    | uu____26393::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26449  ->
    let uu____26450 = FStar_ST.op_Bang last_env in
    match uu____26450 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___417_26511 = hd1 in
          {
            bindings = (uu___417_26511.bindings);
            depth = (uu___417_26511.depth);
            tcenv = (uu___417_26511.tcenv);
            warn = (uu___417_26511.warn);
            cache = refs;
            nolabels = (uu___417_26511.nolabels);
            use_zfuel_name = (uu___417_26511.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___417_26511.encode_non_total_function_typ);
            current_module_name = (uu___417_26511.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26564  ->
    let uu____26565 = FStar_ST.op_Bang last_env in
    match uu____26565 with
    | [] -> failwith "Popping an empty stack"
    | uu____26618::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26709::uu____26710,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___418_26718 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___418_26718.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___418_26718.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___418_26718.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26719 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26734 =
        let uu____26737 =
          let uu____26738 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26738 in
        let uu____26739 = open_fact_db_tags env in uu____26737 :: uu____26739 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26734
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
      let uu____26761 = encode_sigelt env se in
      match uu____26761 with
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
        let uu____26797 = FStar_Options.log_queries () in
        if uu____26797
        then
          let uu____26800 =
            let uu____26801 =
              let uu____26802 =
                let uu____26803 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26803 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26802 in
            FStar_SMTEncoding_Term.Caption uu____26801 in
          uu____26800 :: decls
        else decls in
      (let uu____26814 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26814
       then
         let uu____26815 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26815
       else ());
      (let env =
         let uu____26818 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26818 tcenv in
       let uu____26819 = encode_top_level_facts env se in
       match uu____26819 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26833 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26833)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26845 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26845
       then
         let uu____26846 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26846
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26881  ->
                 fun se  ->
                   match uu____26881 with
                   | (g,env2) ->
                       let uu____26901 = encode_top_level_facts env2 se in
                       (match uu____26901 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26924 =
         encode_signature
           (let uu___419_26933 = env in
            {
              bindings = (uu___419_26933.bindings);
              depth = (uu___419_26933.depth);
              tcenv = (uu___419_26933.tcenv);
              warn = false;
              cache = (uu___419_26933.cache);
              nolabels = (uu___419_26933.nolabels);
              use_zfuel_name = (uu___419_26933.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___419_26933.encode_non_total_function_typ);
              current_module_name = (uu___419_26933.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26924 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26950 = FStar_Options.log_queries () in
             if uu____26950
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___420_26958 = env1 in
               {
                 bindings = (uu___420_26958.bindings);
                 depth = (uu___420_26958.depth);
                 tcenv = (uu___420_26958.tcenv);
                 warn = true;
                 cache = (uu___420_26958.cache);
                 nolabels = (uu___420_26958.nolabels);
                 use_zfuel_name = (uu___420_26958.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___420_26958.encode_non_total_function_typ);
                 current_module_name = (uu___420_26958.current_module_name)
               });
            (let uu____26960 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26960
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
        (let uu____27012 =
           let uu____27013 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27013.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27012);
        (let env =
           let uu____27015 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27015 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27027 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27062 = aux rest in
                 (match uu____27062 with
                  | (out,rest1) ->
                      let t =
                        let uu____27092 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27092 with
                        | FStar_Pervasives_Native.Some uu____27097 ->
                            let uu____27098 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27098
                              x.FStar_Syntax_Syntax.sort
                        | uu____27099 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27103 =
                        let uu____27106 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___421_27109 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___421_27109.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___421_27109.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27106 :: out in
                      (uu____27103, rest1))
             | uu____27114 -> ([], bindings1) in
           let uu____27121 = aux bindings in
           match uu____27121 with
           | (closing,bindings1) ->
               let uu____27146 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27146, bindings1) in
         match uu____27027 with
         | (q1,bindings1) ->
             let uu____27169 =
               let uu____27174 =
                 FStar_List.filter
                   (fun uu___386_27179  ->
                      match uu___386_27179 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27180 ->
                          false
                      | uu____27187 -> true) bindings1 in
               encode_env_bindings env uu____27174 in
             (match uu____27169 with
              | (env_decls,env1) ->
                  ((let uu____27205 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27205
                    then
                      let uu____27206 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27206
                    else ());
                   (let uu____27208 = encode_formula q1 env1 in
                    match uu____27208 with
                    | (phi,qdecls) ->
                        let uu____27229 =
                          let uu____27234 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27234 phi in
                        (match uu____27229 with
                         | (labels,phi1) ->
                             let uu____27251 = encode_labels labels in
                             (match uu____27251 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27288 =
                                      let uu____27295 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27296 =
                                        varops.mk_unique "@query" in
                                      (uu____27295,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27296) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27288 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))