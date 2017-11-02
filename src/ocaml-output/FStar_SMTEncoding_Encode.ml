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
      (fun uu___362_107  ->
         match uu___362_107 with
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
        let uu___385_203 = a in
        let uu____204 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____204;
          FStar_Syntax_Syntax.index =
            (uu___385_203.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___385_203.FStar_Syntax_Syntax.sort)
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
    let uu___386_1847 = x in
    let uu____1848 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1848;
      FStar_Syntax_Syntax.index = (uu___386_1847.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___386_1847.FStar_Syntax_Syntax.sort)
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
                 (fun uu___363_2295  ->
                    match uu___363_2295 with
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
           (fun uu___364_2318  ->
              match uu___364_2318 with
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
        (let uu___387_2398 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___387_2398.tcenv);
           warn = (uu___387_2398.warn);
           cache = (uu___387_2398.cache);
           nolabels = (uu___387_2398.nolabels);
           use_zfuel_name = (uu___387_2398.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___387_2398.encode_non_total_function_typ);
           current_module_name = (uu___387_2398.current_module_name)
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
        (let uu___388_2416 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___388_2416.depth);
           tcenv = (uu___388_2416.tcenv);
           warn = (uu___388_2416.warn);
           cache = (uu___388_2416.cache);
           nolabels = (uu___388_2416.nolabels);
           use_zfuel_name = (uu___388_2416.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___388_2416.encode_non_total_function_typ);
           current_module_name = (uu___388_2416.current_module_name)
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
          (let uu___389_2437 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___389_2437.depth);
             tcenv = (uu___389_2437.tcenv);
             warn = (uu___389_2437.warn);
             cache = (uu___389_2437.cache);
             nolabels = (uu___389_2437.nolabels);
             use_zfuel_name = (uu___389_2437.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___389_2437.encode_non_total_function_typ);
             current_module_name = (uu___389_2437.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___390_2447 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___390_2447.depth);
          tcenv = (uu___390_2447.tcenv);
          warn = (uu___390_2447.warn);
          cache = (uu___390_2447.cache);
          nolabels = (uu___390_2447.nolabels);
          use_zfuel_name = (uu___390_2447.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___390_2447.encode_non_total_function_typ);
          current_module_name = (uu___390_2447.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___365_2471  ->
             match uu___365_2471 with
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
        let uu___391_2542 = env in
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
          depth = (uu___391_2542.depth);
          tcenv = (uu___391_2542.tcenv);
          warn = (uu___391_2542.warn);
          cache = (uu___391_2542.cache);
          nolabels = (uu___391_2542.nolabels);
          use_zfuel_name = (uu___391_2542.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___391_2542.encode_non_total_function_typ);
          current_module_name = (uu___391_2542.current_module_name)
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
        (fun uu___366_2605  ->
           match uu___366_2605 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2644 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2661 =
        lookup_binding env
          (fun uu___367_2669  ->
             match uu___367_2669 with
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
          let uu___392_2785 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___392_2785.depth);
            tcenv = (uu___392_2785.tcenv);
            warn = (uu___392_2785.warn);
            cache = (uu___392_2785.cache);
            nolabels = (uu___392_2785.nolabels);
            use_zfuel_name = (uu___392_2785.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___392_2785.encode_non_total_function_typ);
            current_module_name = (uu___392_2785.current_module_name)
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
            let uu___393_2837 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___393_2837.depth);
              tcenv = (uu___393_2837.tcenv);
              warn = (uu___393_2837.warn);
              cache = (uu___393_2837.cache);
              nolabels = (uu___393_2837.nolabels);
              use_zfuel_name = (uu___393_2837.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___393_2837.encode_non_total_function_typ);
              current_module_name = (uu___393_2837.current_module_name)
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
        (fun uu___368_3081  ->
           match uu___368_3081 with
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
               (fun uu___369_3400  ->
                  match uu___369_3400 with
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
  fun uu___370_3498  ->
    match uu___370_3498 with
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
                           (let uu___394_6220 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___394_6220.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___394_6220.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___394_6220.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___394_6220.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___394_6220.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___394_6220.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___394_6220.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___394_6220.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___394_6220.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___394_6220.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___394_6220.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___394_6220.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___394_6220.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___394_6220.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___394_6220.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___394_6220.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___394_6220.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___394_6220.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___394_6220.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___394_6220.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___394_6220.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___394_6220.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___394_6220.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___394_6220.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___394_6220.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___394_6220.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___394_6220.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___394_6220.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___394_6220.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___394_6220.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___394_6220.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___394_6220.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___394_6220.FStar_TypeChecker_Env.dep_graph)
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
                         let uu____8241 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8241 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8240);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8243 =
                       (is_impure rc) &&
                         (let uu____8245 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8245) in
                     if uu____8243
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8252 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8252 with
                        | (vars,guards,envbody,decls,uu____8277) ->
                            let body2 =
                              let uu____8291 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8291
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8293 = encode_term body2 envbody in
                            (match uu____8293 with
                             | (body3,decls') ->
                                 let uu____8304 =
                                   let uu____8313 = codomain_eff rc in
                                   match uu____8313 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8332 = encode_term tfun env in
                                       (match uu____8332 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8304 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8364 =
                                          let uu____8375 =
                                            let uu____8376 =
                                              let uu____8381 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8381, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8376 in
                                          ([], vars, uu____8375) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8364 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8393 =
                                              let uu____8396 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8396
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8393 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8415 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8415 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8423 =
                                             let uu____8424 =
                                               let uu____8431 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8431) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8424 in
                                           (uu____8423,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8442 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8442 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8453 =
                                                    let uu____8454 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8454 = cache_size in
                                                  if uu____8453
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
                                                    let uu____8470 =
                                                      let uu____8471 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8471 in
                                                    varops.mk_unique
                                                      uu____8470 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8478 =
                                                    let uu____8485 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8485) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8478 in
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
                                                      let uu____8503 =
                                                        let uu____8504 =
                                                          let uu____8511 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8511,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8504 in
                                                      [uu____8503] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8524 =
                                                    let uu____8531 =
                                                      let uu____8532 =
                                                        let uu____8543 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8543) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8532 in
                                                    (uu____8531,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8524 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8560 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8560);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8563,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8564;
                          FStar_Syntax_Syntax.lbunivs = uu____8565;
                          FStar_Syntax_Syntax.lbtyp = uu____8566;
                          FStar_Syntax_Syntax.lbeff = uu____8567;
                          FStar_Syntax_Syntax.lbdef = uu____8568;_}::uu____8569),uu____8570)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8596;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8598;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8619 ->
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
              let uu____8689 = encode_term e1 env in
              match uu____8689 with
              | (ee1,decls1) ->
                  let uu____8700 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8700 with
                   | (xs,e21) ->
                       let uu____8725 = FStar_List.hd xs in
                       (match uu____8725 with
                        | (x1,uu____8739) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8741 = encode_body e21 env' in
                            (match uu____8741 with
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
            let uu____8773 =
              let uu____8780 =
                let uu____8781 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8781 in
              gen_term_var env uu____8780 in
            match uu____8773 with
            | (scrsym,scr',env1) ->
                let uu____8789 = encode_term e env1 in
                (match uu____8789 with
                 | (scr,decls) ->
                     let uu____8800 =
                       let encode_branch b uu____8825 =
                         match uu____8825 with
                         | (else_case,decls1) ->
                             let uu____8844 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8844 with
                              | (p,w,br) ->
                                  let uu____8870 = encode_pat env1 p in
                                  (match uu____8870 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8907  ->
                                                   match uu____8907 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8914 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8936 =
                                               encode_term w1 env2 in
                                             (match uu____8936 with
                                              | (w2,decls2) ->
                                                  let uu____8949 =
                                                    let uu____8950 =
                                                      let uu____8955 =
                                                        let uu____8956 =
                                                          let uu____8961 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8961) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8956 in
                                                      (guard, uu____8955) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8950 in
                                                  (uu____8949, decls2)) in
                                       (match uu____8914 with
                                        | (guard1,decls2) ->
                                            let uu____8974 =
                                              encode_br br env2 in
                                            (match uu____8974 with
                                             | (br1,decls3) ->
                                                 let uu____8987 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8987,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8800 with
                      | (match_tm,decls1) ->
                          let uu____9006 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9006, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9046 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9046
       then
         let uu____9047 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9047
       else ());
      (let uu____9049 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9049 with
       | (vars,pat_term) ->
           let uu____9066 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9119  ->
                     fun v1  ->
                       match uu____9119 with
                       | (env1,vars1) ->
                           let uu____9171 = gen_term_var env1 v1 in
                           (match uu____9171 with
                            | (xx,uu____9193,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9066 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9272 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9273 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9274 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9282 = encode_const c env1 in
                      (match uu____9282 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9296::uu____9297 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9300 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9323 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9323 with
                        | (uu____9330,uu____9331::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9334 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9367  ->
                                  match uu____9367 with
                                  | (arg,uu____9375) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9381 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9381)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9408) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9439 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9462 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9506  ->
                                  match uu____9506 with
                                  | (arg,uu____9520) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9526 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9526)) in
                      FStar_All.pipe_right uu____9462 FStar_List.flatten in
                let pat_term1 uu____9554 = encode_term pat_term env1 in
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
      let uu____9564 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9602  ->
                fun uu____9603  ->
                  match (uu____9602, uu____9603) with
                  | ((tms,decls),(t,uu____9639)) ->
                      let uu____9660 = encode_term t env in
                      (match uu____9660 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9564 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9717 = FStar_Syntax_Util.list_elements e in
        match uu____9717 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9738 =
          let uu____9753 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9753 FStar_Syntax_Util.head_and_args in
        match uu____9738 with
        | (head1,args) ->
            let uu____9792 =
              let uu____9805 =
                let uu____9806 = FStar_Syntax_Util.un_uinst head1 in
                uu____9806.FStar_Syntax_Syntax.n in
              (uu____9805, args) in
            (match uu____9792 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9820,uu____9821)::(e,uu____9823)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9858 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9894 =
            let uu____9909 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9909 FStar_Syntax_Util.head_and_args in
          match uu____9894 with
          | (head1,args) ->
              let uu____9950 =
                let uu____9963 =
                  let uu____9964 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9964.FStar_Syntax_Syntax.n in
                (uu____9963, args) in
              (match uu____9950 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9981)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10008 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10030 = smt_pat_or1 t1 in
            (match uu____10030 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10046 = list_elements1 e in
                 FStar_All.pipe_right uu____10046
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10064 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10064
                           (FStar_List.map one_pat)))
             | uu____10075 ->
                 let uu____10080 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10080])
        | uu____10101 ->
            let uu____10104 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10104] in
      let uu____10125 =
        let uu____10144 =
          let uu____10145 = FStar_Syntax_Subst.compress t in
          uu____10145.FStar_Syntax_Syntax.n in
        match uu____10144 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10184 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10184 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10227;
                        FStar_Syntax_Syntax.effect_name = uu____10228;
                        FStar_Syntax_Syntax.result_typ = uu____10229;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10231)::(post,uu____10233)::(pats,uu____10235)::[];
                        FStar_Syntax_Syntax.flags = uu____10236;_}
                      ->
                      let uu____10277 = lemma_pats pats in
                      (binders1, pre, post, uu____10277)
                  | uu____10294 -> failwith "impos"))
        | uu____10313 -> failwith "Impos" in
      match uu____10125 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___395_10361 = env in
            {
              bindings = (uu___395_10361.bindings);
              depth = (uu___395_10361.depth);
              tcenv = (uu___395_10361.tcenv);
              warn = (uu___395_10361.warn);
              cache = (uu___395_10361.cache);
              nolabels = (uu___395_10361.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___395_10361.encode_non_total_function_typ);
              current_module_name = (uu___395_10361.current_module_name)
            } in
          let uu____10362 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10362 with
           | (vars,guards,env2,decls,uu____10387) ->
               let uu____10400 =
                 let uu____10413 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10457 =
                             let uu____10466 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10466
                               FStar_List.unzip in
                           match uu____10457 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10413 FStar_List.unzip in
               (match uu____10400 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___396_10578 = env2 in
                      {
                        bindings = (uu___396_10578.bindings);
                        depth = (uu___396_10578.depth);
                        tcenv = (uu___396_10578.tcenv);
                        warn = (uu___396_10578.warn);
                        cache = (uu___396_10578.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___396_10578.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___396_10578.encode_non_total_function_typ);
                        current_module_name =
                          (uu___396_10578.current_module_name)
                      } in
                    let uu____10579 =
                      let uu____10584 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10584 env3 in
                    (match uu____10579 with
                     | (pre1,decls'') ->
                         let uu____10591 =
                           let uu____10596 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10596 env3 in
                         (match uu____10591 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10606 =
                                let uu____10607 =
                                  let uu____10618 =
                                    let uu____10619 =
                                      let uu____10624 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10624, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10619 in
                                  (pats, vars, uu____10618) in
                                FStar_SMTEncoding_Util.mkForall uu____10607 in
                              (uu____10606, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10643 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10643
        then
          let uu____10644 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10645 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10644 uu____10645
        else () in
      let enc f r l =
        let uu____10678 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10706 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10706 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10678 with
        | (decls,args) ->
            let uu____10735 =
              let uu___397_10736 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___397_10736.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___397_10736.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10735, decls) in
      let const_op f r uu____10767 =
        let uu____10780 = f r in (uu____10780, []) in
      let un_op f l =
        let uu____10799 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10799 in
      let bin_op f uu___371_10815 =
        match uu___371_10815 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10826 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10860 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10883  ->
                 match uu____10883 with
                 | (t,uu____10897) ->
                     let uu____10898 = encode_formula t env in
                     (match uu____10898 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10860 with
        | (decls,phis) ->
            let uu____10927 =
              let uu___398_10928 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___398_10928.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___398_10928.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10927, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10989  ->
               match uu____10989 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11008) -> false
                    | uu____11009 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11024 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11024
        else
          (let uu____11038 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11038 r rf) in
      let mk_imp1 r uu___372_11063 =
        match uu___372_11063 with
        | (lhs,uu____11069)::(rhs,uu____11071)::[] ->
            let uu____11098 = encode_formula rhs env in
            (match uu____11098 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11113) ->
                      (l1, decls1)
                  | uu____11118 ->
                      let uu____11119 = encode_formula lhs env in
                      (match uu____11119 with
                       | (l2,decls2) ->
                           let uu____11130 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11130, (FStar_List.append decls1 decls2)))))
        | uu____11133 -> failwith "impossible" in
      let mk_ite r uu___373_11154 =
        match uu___373_11154 with
        | (guard,uu____11160)::(_then,uu____11162)::(_else,uu____11164)::[]
            ->
            let uu____11201 = encode_formula guard env in
            (match uu____11201 with
             | (g,decls1) ->
                 let uu____11212 = encode_formula _then env in
                 (match uu____11212 with
                  | (t,decls2) ->
                      let uu____11223 = encode_formula _else env in
                      (match uu____11223 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11237 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11262 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11262 in
      let connectives =
        let uu____11280 =
          let uu____11293 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11293) in
        let uu____11310 =
          let uu____11325 =
            let uu____11338 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11338) in
          let uu____11355 =
            let uu____11370 =
              let uu____11385 =
                let uu____11398 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11398) in
              let uu____11415 =
                let uu____11430 =
                  let uu____11445 =
                    let uu____11458 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11458) in
                  [uu____11445;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11430 in
              uu____11385 :: uu____11415 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11370 in
          uu____11325 :: uu____11355 in
        uu____11280 :: uu____11310 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11779 = encode_formula phi' env in
            (match uu____11779 with
             | (phi2,decls) ->
                 let uu____11790 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11790, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11791 ->
            let uu____11798 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11798 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11837 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11837 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11849;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11851;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11872 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11872 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11919::(x,uu____11921)::(t,uu____11923)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11970 = encode_term x env in
                 (match uu____11970 with
                  | (x1,decls) ->
                      let uu____11981 = encode_term t env in
                      (match uu____11981 with
                       | (t1,decls') ->
                           let uu____11992 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____11992, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11997)::(msg,uu____11999)::(phi2,uu____12001)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12046 =
                   let uu____12051 =
                     let uu____12052 = FStar_Syntax_Subst.compress r in
                     uu____12052.FStar_Syntax_Syntax.n in
                   let uu____12055 =
                     let uu____12056 = FStar_Syntax_Subst.compress msg in
                     uu____12056.FStar_Syntax_Syntax.n in
                   (uu____12051, uu____12055) in
                 (match uu____12046 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12065))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12071 -> fallback phi2)
             | uu____12076 when head_redex env head2 ->
                 let uu____12089 = whnf env phi1 in
                 encode_formula uu____12089 env
             | uu____12090 ->
                 let uu____12103 = encode_term phi1 env in
                 (match uu____12103 with
                  | (tt,decls) ->
                      let uu____12114 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___399_12117 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___399_12117.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___399_12117.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12114, decls)))
        | uu____12118 ->
            let uu____12119 = encode_term phi1 env in
            (match uu____12119 with
             | (tt,decls) ->
                 let uu____12130 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___400_12133 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___400_12133.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___400_12133.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12130, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12169 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12169 with
        | (vars,guards,env2,decls,uu____12208) ->
            let uu____12221 =
              let uu____12234 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12282 =
                          let uu____12291 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12321  ->
                                    match uu____12321 with
                                    | (t,uu____12331) ->
                                        encode_term t
                                          (let uu___401_12333 = env2 in
                                           {
                                             bindings =
                                               (uu___401_12333.bindings);
                                             depth = (uu___401_12333.depth);
                                             tcenv = (uu___401_12333.tcenv);
                                             warn = (uu___401_12333.warn);
                                             cache = (uu___401_12333.cache);
                                             nolabels =
                                               (uu___401_12333.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___401_12333.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___401_12333.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12291 FStar_List.unzip in
                        match uu____12282 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12234 FStar_List.unzip in
            (match uu____12221 with
             | (pats,decls') ->
                 let uu____12432 = encode_formula body env2 in
                 (match uu____12432 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12464;
                             FStar_SMTEncoding_Term.rng = uu____12465;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12480 -> guards in
                      let uu____12485 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12485, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12545  ->
                   match uu____12545 with
                   | (x,uu____12551) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12559 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12571 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12571) uu____12559 tl1 in
             let uu____12574 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12601  ->
                       match uu____12601 with
                       | (b,uu____12607) ->
                           let uu____12608 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12608)) in
             (match uu____12574 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12614) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12628 =
                    let uu____12629 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12629 in
                  FStar_Errors.warn pos uu____12628) in
       let uu____12630 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12630 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12639 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12697  ->
                     match uu____12697 with
                     | (l,uu____12711) -> FStar_Ident.lid_equals op l)) in
           (match uu____12639 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12744,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12784 = encode_q_body env vars pats body in
             match uu____12784 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12829 =
                     let uu____12840 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12840) in
                   FStar_SMTEncoding_Term.mkForall uu____12829
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12859 = encode_q_body env vars pats body in
             match uu____12859 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12903 =
                   let uu____12904 =
                     let uu____12915 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12915) in
                   FStar_SMTEncoding_Term.mkExists uu____12904
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12903, decls))))
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
  let uu____13008 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13008 with
  | (asym,a) ->
      let uu____13015 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13015 with
       | (xsym,x) ->
           let uu____13022 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13022 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13066 =
                      let uu____13077 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13077, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13066 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13103 =
                      let uu____13110 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13110) in
                    FStar_SMTEncoding_Util.mkApp uu____13103 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13123 =
                    let uu____13126 =
                      let uu____13129 =
                        let uu____13132 =
                          let uu____13133 =
                            let uu____13140 =
                              let uu____13141 =
                                let uu____13152 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13152) in
                              FStar_SMTEncoding_Util.mkForall uu____13141 in
                            (uu____13140, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13133 in
                        let uu____13169 =
                          let uu____13172 =
                            let uu____13173 =
                              let uu____13180 =
                                let uu____13181 =
                                  let uu____13192 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13192) in
                                FStar_SMTEncoding_Util.mkForall uu____13181 in
                              (uu____13180,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13173 in
                          [uu____13172] in
                        uu____13132 :: uu____13169 in
                      xtok_decl :: uu____13129 in
                    xname_decl :: uu____13126 in
                  (xtok1, uu____13123) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13283 =
                    let uu____13296 =
                      let uu____13305 =
                        let uu____13306 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13306 in
                      quant axy uu____13305 in
                    (FStar_Parser_Const.op_Eq, uu____13296) in
                  let uu____13315 =
                    let uu____13330 =
                      let uu____13343 =
                        let uu____13352 =
                          let uu____13353 =
                            let uu____13354 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13354 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13353 in
                        quant axy uu____13352 in
                      (FStar_Parser_Const.op_notEq, uu____13343) in
                    let uu____13363 =
                      let uu____13378 =
                        let uu____13391 =
                          let uu____13400 =
                            let uu____13401 =
                              let uu____13402 =
                                let uu____13407 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13408 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13407, uu____13408) in
                              FStar_SMTEncoding_Util.mkLT uu____13402 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13401 in
                          quant xy uu____13400 in
                        (FStar_Parser_Const.op_LT, uu____13391) in
                      let uu____13417 =
                        let uu____13432 =
                          let uu____13445 =
                            let uu____13454 =
                              let uu____13455 =
                                let uu____13456 =
                                  let uu____13461 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13462 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13461, uu____13462) in
                                FStar_SMTEncoding_Util.mkLTE uu____13456 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13455 in
                            quant xy uu____13454 in
                          (FStar_Parser_Const.op_LTE, uu____13445) in
                        let uu____13471 =
                          let uu____13486 =
                            let uu____13499 =
                              let uu____13508 =
                                let uu____13509 =
                                  let uu____13510 =
                                    let uu____13515 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13516 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13515, uu____13516) in
                                  FStar_SMTEncoding_Util.mkGT uu____13510 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13509 in
                              quant xy uu____13508 in
                            (FStar_Parser_Const.op_GT, uu____13499) in
                          let uu____13525 =
                            let uu____13540 =
                              let uu____13553 =
                                let uu____13562 =
                                  let uu____13563 =
                                    let uu____13564 =
                                      let uu____13569 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13570 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13569, uu____13570) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13564 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13563 in
                                quant xy uu____13562 in
                              (FStar_Parser_Const.op_GTE, uu____13553) in
                            let uu____13579 =
                              let uu____13594 =
                                let uu____13607 =
                                  let uu____13616 =
                                    let uu____13617 =
                                      let uu____13618 =
                                        let uu____13623 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13624 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13623, uu____13624) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13618 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13617 in
                                  quant xy uu____13616 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13607) in
                              let uu____13633 =
                                let uu____13648 =
                                  let uu____13661 =
                                    let uu____13670 =
                                      let uu____13671 =
                                        let uu____13672 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13672 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13671 in
                                    quant qx uu____13670 in
                                  (FStar_Parser_Const.op_Minus, uu____13661) in
                                let uu____13681 =
                                  let uu____13696 =
                                    let uu____13709 =
                                      let uu____13718 =
                                        let uu____13719 =
                                          let uu____13720 =
                                            let uu____13725 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13726 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13725, uu____13726) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13720 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13719 in
                                      quant xy uu____13718 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13709) in
                                  let uu____13735 =
                                    let uu____13750 =
                                      let uu____13763 =
                                        let uu____13772 =
                                          let uu____13773 =
                                            let uu____13774 =
                                              let uu____13779 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13780 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13779, uu____13780) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13774 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13773 in
                                        quant xy uu____13772 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13763) in
                                    let uu____13789 =
                                      let uu____13804 =
                                        let uu____13817 =
                                          let uu____13826 =
                                            let uu____13827 =
                                              let uu____13828 =
                                                let uu____13833 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13834 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13833, uu____13834) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13828 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13827 in
                                          quant xy uu____13826 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13817) in
                                      let uu____13843 =
                                        let uu____13858 =
                                          let uu____13871 =
                                            let uu____13880 =
                                              let uu____13881 =
                                                let uu____13882 =
                                                  let uu____13887 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13888 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13887, uu____13888) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13882 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13881 in
                                            quant xy uu____13880 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13871) in
                                        let uu____13897 =
                                          let uu____13912 =
                                            let uu____13925 =
                                              let uu____13934 =
                                                let uu____13935 =
                                                  let uu____13936 =
                                                    let uu____13941 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13942 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13941,
                                                      uu____13942) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13936 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13935 in
                                              quant xy uu____13934 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13925) in
                                          let uu____13951 =
                                            let uu____13966 =
                                              let uu____13979 =
                                                let uu____13988 =
                                                  let uu____13989 =
                                                    let uu____13990 =
                                                      let uu____13995 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____13996 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____13995,
                                                        uu____13996) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13990 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13989 in
                                                quant xy uu____13988 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13979) in
                                            let uu____14005 =
                                              let uu____14020 =
                                                let uu____14033 =
                                                  let uu____14042 =
                                                    let uu____14043 =
                                                      let uu____14044 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14044 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14043 in
                                                  quant qx uu____14042 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14033) in
                                              [uu____14020] in
                                            uu____13966 :: uu____14005 in
                                          uu____13912 :: uu____13951 in
                                        uu____13858 :: uu____13897 in
                                      uu____13804 :: uu____13843 in
                                    uu____13750 :: uu____13789 in
                                  uu____13696 :: uu____13735 in
                                uu____13648 :: uu____13681 in
                              uu____13594 :: uu____13633 in
                            uu____13540 :: uu____13579 in
                          uu____13486 :: uu____13525 in
                        uu____13432 :: uu____13471 in
                      uu____13378 :: uu____13417 in
                    uu____13330 :: uu____13363 in
                  uu____13283 :: uu____13315 in
                let mk1 l v1 =
                  let uu____14258 =
                    let uu____14267 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14325  ->
                              match uu____14325 with
                              | (l',uu____14339) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14267
                      (FStar_Option.map
                         (fun uu____14399  ->
                            match uu____14399 with | (uu____14418,b) -> b v1)) in
                  FStar_All.pipe_right uu____14258 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14489  ->
                          match uu____14489 with
                          | (l',uu____14503) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14541 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14541 with
        | (xxsym,xx) ->
            let uu____14548 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14548 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14558 =
                   let uu____14565 =
                     let uu____14566 =
                       let uu____14577 =
                         let uu____14578 =
                           let uu____14583 =
                             let uu____14584 =
                               let uu____14589 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14589) in
                             FStar_SMTEncoding_Util.mkEq uu____14584 in
                           (xx_has_type, uu____14583) in
                         FStar_SMTEncoding_Util.mkImp uu____14578 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14577) in
                     FStar_SMTEncoding_Util.mkForall uu____14566 in
                   let uu____14614 =
                     let uu____14615 =
                       let uu____14616 =
                         let uu____14617 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14617 in
                       Prims.strcat module_name uu____14616 in
                     varops.mk_unique uu____14615 in
                   (uu____14565, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14614) in
                 FStar_SMTEncoding_Util.mkAssume uu____14558)
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
    let uu____14653 =
      let uu____14654 =
        let uu____14661 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14661, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14654 in
    let uu____14664 =
      let uu____14667 =
        let uu____14668 =
          let uu____14675 =
            let uu____14676 =
              let uu____14687 =
                let uu____14688 =
                  let uu____14693 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14693) in
                FStar_SMTEncoding_Util.mkImp uu____14688 in
              ([[typing_pred]], [xx], uu____14687) in
            mkForall_fuel uu____14676 in
          (uu____14675, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14668 in
      [uu____14667] in
    uu____14653 :: uu____14664 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14735 =
      let uu____14736 =
        let uu____14743 =
          let uu____14744 =
            let uu____14755 =
              let uu____14760 =
                let uu____14763 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14763] in
              [uu____14760] in
            let uu____14768 =
              let uu____14769 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14769 tt in
            (uu____14755, [bb], uu____14768) in
          FStar_SMTEncoding_Util.mkForall uu____14744 in
        (uu____14743, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14736 in
    let uu____14790 =
      let uu____14793 =
        let uu____14794 =
          let uu____14801 =
            let uu____14802 =
              let uu____14813 =
                let uu____14814 =
                  let uu____14819 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14819) in
                FStar_SMTEncoding_Util.mkImp uu____14814 in
              ([[typing_pred]], [xx], uu____14813) in
            mkForall_fuel uu____14802 in
          (uu____14801, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14794 in
      [uu____14793] in
    uu____14735 :: uu____14790 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14869 =
        let uu____14870 =
          let uu____14877 =
            let uu____14880 =
              let uu____14883 =
                let uu____14886 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14887 =
                  let uu____14890 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14890] in
                uu____14886 :: uu____14887 in
              tt :: uu____14883 in
            tt :: uu____14880 in
          ("Prims.Precedes", uu____14877) in
        FStar_SMTEncoding_Util.mkApp uu____14870 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14869 in
    let precedes_y_x =
      let uu____14894 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14894 in
    let uu____14897 =
      let uu____14898 =
        let uu____14905 =
          let uu____14906 =
            let uu____14917 =
              let uu____14922 =
                let uu____14925 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14925] in
              [uu____14922] in
            let uu____14930 =
              let uu____14931 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14931 tt in
            (uu____14917, [bb], uu____14930) in
          FStar_SMTEncoding_Util.mkForall uu____14906 in
        (uu____14905, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14898 in
    let uu____14952 =
      let uu____14955 =
        let uu____14956 =
          let uu____14963 =
            let uu____14964 =
              let uu____14975 =
                let uu____14976 =
                  let uu____14981 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14981) in
                FStar_SMTEncoding_Util.mkImp uu____14976 in
              ([[typing_pred]], [xx], uu____14975) in
            mkForall_fuel uu____14964 in
          (uu____14963, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14956 in
      let uu____15006 =
        let uu____15009 =
          let uu____15010 =
            let uu____15017 =
              let uu____15018 =
                let uu____15029 =
                  let uu____15030 =
                    let uu____15035 =
                      let uu____15036 =
                        let uu____15039 =
                          let uu____15042 =
                            let uu____15045 =
                              let uu____15046 =
                                let uu____15051 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15052 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15051, uu____15052) in
                              FStar_SMTEncoding_Util.mkGT uu____15046 in
                            let uu____15053 =
                              let uu____15056 =
                                let uu____15057 =
                                  let uu____15062 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15063 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15062, uu____15063) in
                                FStar_SMTEncoding_Util.mkGTE uu____15057 in
                              let uu____15064 =
                                let uu____15067 =
                                  let uu____15068 =
                                    let uu____15073 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15074 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15073, uu____15074) in
                                  FStar_SMTEncoding_Util.mkLT uu____15068 in
                                [uu____15067] in
                              uu____15056 :: uu____15064 in
                            uu____15045 :: uu____15053 in
                          typing_pred_y :: uu____15042 in
                        typing_pred :: uu____15039 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15036 in
                    (uu____15035, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15030 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15029) in
              mkForall_fuel uu____15018 in
            (uu____15017,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15010 in
        [uu____15009] in
      uu____14955 :: uu____15006 in
    uu____14897 :: uu____14952 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15120 =
      let uu____15121 =
        let uu____15128 =
          let uu____15129 =
            let uu____15140 =
              let uu____15145 =
                let uu____15148 = FStar_SMTEncoding_Term.boxString b in
                [uu____15148] in
              [uu____15145] in
            let uu____15153 =
              let uu____15154 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15154 tt in
            (uu____15140, [bb], uu____15153) in
          FStar_SMTEncoding_Util.mkForall uu____15129 in
        (uu____15128, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15121 in
    let uu____15175 =
      let uu____15178 =
        let uu____15179 =
          let uu____15186 =
            let uu____15187 =
              let uu____15198 =
                let uu____15199 =
                  let uu____15204 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15204) in
                FStar_SMTEncoding_Util.mkImp uu____15199 in
              ([[typing_pred]], [xx], uu____15198) in
            mkForall_fuel uu____15187 in
          (uu____15186, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15179 in
      [uu____15178] in
    uu____15120 :: uu____15175 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15257 =
      let uu____15258 =
        let uu____15265 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15265, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15258 in
    [uu____15257] in
  let mk_and_interp env conj uu____15277 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15302 =
      let uu____15303 =
        let uu____15310 =
          let uu____15311 =
            let uu____15322 =
              let uu____15323 =
                let uu____15328 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15328, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15323 in
            ([[l_and_a_b]], [aa; bb], uu____15322) in
          FStar_SMTEncoding_Util.mkForall uu____15311 in
        (uu____15310, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15303 in
    [uu____15302] in
  let mk_or_interp env disj uu____15366 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15391 =
      let uu____15392 =
        let uu____15399 =
          let uu____15400 =
            let uu____15411 =
              let uu____15412 =
                let uu____15417 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15417, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15412 in
            ([[l_or_a_b]], [aa; bb], uu____15411) in
          FStar_SMTEncoding_Util.mkForall uu____15400 in
        (uu____15399, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15392 in
    [uu____15391] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15480 =
      let uu____15481 =
        let uu____15488 =
          let uu____15489 =
            let uu____15500 =
              let uu____15501 =
                let uu____15506 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15506, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15501 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15500) in
          FStar_SMTEncoding_Util.mkForall uu____15489 in
        (uu____15488, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15481 in
    [uu____15480] in
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
    let uu____15579 =
      let uu____15580 =
        let uu____15587 =
          let uu____15588 =
            let uu____15599 =
              let uu____15600 =
                let uu____15605 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15605, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15600 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15599) in
          FStar_SMTEncoding_Util.mkForall uu____15588 in
        (uu____15587, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15580 in
    [uu____15579] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15676 =
      let uu____15677 =
        let uu____15684 =
          let uu____15685 =
            let uu____15696 =
              let uu____15697 =
                let uu____15702 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15702, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15697 in
            ([[l_imp_a_b]], [aa; bb], uu____15696) in
          FStar_SMTEncoding_Util.mkForall uu____15685 in
        (uu____15684, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15677 in
    [uu____15676] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15765 =
      let uu____15766 =
        let uu____15773 =
          let uu____15774 =
            let uu____15785 =
              let uu____15786 =
                let uu____15791 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15791, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15786 in
            ([[l_iff_a_b]], [aa; bb], uu____15785) in
          FStar_SMTEncoding_Util.mkForall uu____15774 in
        (uu____15773, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15766 in
    [uu____15765] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15843 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15843 in
    let uu____15846 =
      let uu____15847 =
        let uu____15854 =
          let uu____15855 =
            let uu____15866 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15866) in
          FStar_SMTEncoding_Util.mkForall uu____15855 in
        (uu____15854, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15847 in
    [uu____15846] in
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
      let uu____15926 =
        let uu____15933 =
          let uu____15936 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15936] in
        ("Valid", uu____15933) in
      FStar_SMTEncoding_Util.mkApp uu____15926 in
    let uu____15939 =
      let uu____15940 =
        let uu____15947 =
          let uu____15948 =
            let uu____15959 =
              let uu____15960 =
                let uu____15965 =
                  let uu____15966 =
                    let uu____15977 =
                      let uu____15982 =
                        let uu____15985 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15985] in
                      [uu____15982] in
                    let uu____15990 =
                      let uu____15991 =
                        let uu____15996 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____15996, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____15991 in
                    (uu____15977, [xx1], uu____15990) in
                  FStar_SMTEncoding_Util.mkForall uu____15966 in
                (uu____15965, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15960 in
            ([[l_forall_a_b]], [aa; bb], uu____15959) in
          FStar_SMTEncoding_Util.mkForall uu____15948 in
        (uu____15947, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15940 in
    [uu____15939] in
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
      let uu____16078 =
        let uu____16085 =
          let uu____16088 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16088] in
        ("Valid", uu____16085) in
      FStar_SMTEncoding_Util.mkApp uu____16078 in
    let uu____16091 =
      let uu____16092 =
        let uu____16099 =
          let uu____16100 =
            let uu____16111 =
              let uu____16112 =
                let uu____16117 =
                  let uu____16118 =
                    let uu____16129 =
                      let uu____16134 =
                        let uu____16137 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16137] in
                      [uu____16134] in
                    let uu____16142 =
                      let uu____16143 =
                        let uu____16148 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16148, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16143 in
                    (uu____16129, [xx1], uu____16142) in
                  FStar_SMTEncoding_Util.mkExists uu____16118 in
                (uu____16117, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16112 in
            ([[l_exists_a_b]], [aa; bb], uu____16111) in
          FStar_SMTEncoding_Util.mkForall uu____16100 in
        (uu____16099, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16092 in
    [uu____16091] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16208 =
      let uu____16209 =
        let uu____16216 =
          let uu____16217 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16217 range_ty in
        let uu____16218 = varops.mk_unique "typing_range_const" in
        (uu____16216, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16218) in
      FStar_SMTEncoding_Util.mkAssume uu____16209 in
    [uu____16208] in
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
        let uu____16252 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16252 x1 t in
      let uu____16253 =
        let uu____16264 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16264) in
      FStar_SMTEncoding_Util.mkForall uu____16253 in
    let uu____16287 =
      let uu____16288 =
        let uu____16295 =
          let uu____16296 =
            let uu____16307 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16307) in
          FStar_SMTEncoding_Util.mkForall uu____16296 in
        (uu____16295,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16288 in
    [uu____16287] in
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
          let uu____16631 =
            FStar_Util.find_opt
              (fun uu____16657  ->
                 match uu____16657 with
                 | (l,uu____16669) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16631 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16694,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16730 = encode_function_type_as_formula t env in
        match uu____16730 with
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
              let uu____16770 =
                ((let uu____16773 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16773) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16770
              then
                let uu____16780 = new_term_constant_and_tok_from_lid env lid in
                match uu____16780 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16799 =
                        let uu____16800 = FStar_Syntax_Subst.compress t_norm in
                        uu____16800.FStar_Syntax_Syntax.n in
                      match uu____16799 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16806) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16836  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16841 -> [] in
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
                (let uu____16855 = prims.is lid in
                 if uu____16855
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16863 = prims.mk lid vname in
                   match uu____16863 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16887 =
                      let uu____16898 = curried_arrow_formals_comp t_norm in
                      match uu____16898 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16916 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16916
                            then
                              let uu____16917 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___402_16920 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___402_16920.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___402_16920.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___402_16920.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___402_16920.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___402_16920.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___402_16920.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___402_16920.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___402_16920.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___402_16920.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___402_16920.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___402_16920.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___402_16920.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___402_16920.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___402_16920.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___402_16920.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___402_16920.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___402_16920.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___402_16920.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___402_16920.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___402_16920.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___402_16920.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___402_16920.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___402_16920.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___402_16920.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___402_16920.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___402_16920.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___402_16920.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___402_16920.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___402_16920.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___402_16920.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___402_16920.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___402_16920.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___402_16920.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16917
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16932 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16932)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16887 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16977 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16977 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____16998 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___374_17040  ->
                                       match uu___374_17040 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17044 =
                                             FStar_Util.prefix vars in
                                           (match uu____17044 with
                                            | (uu____17065,(xxsym,uu____17067))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17085 =
                                                  let uu____17086 =
                                                    let uu____17093 =
                                                      let uu____17094 =
                                                        let uu____17105 =
                                                          let uu____17106 =
                                                            let uu____17111 =
                                                              let uu____17112
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17112 in
                                                            (vapp,
                                                              uu____17111) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17106 in
                                                        ([[vapp]], vars,
                                                          uu____17105) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17094 in
                                                    (uu____17093,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17086 in
                                                [uu____17085])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17131 =
                                             FStar_Util.prefix vars in
                                           (match uu____17131 with
                                            | (uu____17152,(xxsym,uu____17154))
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
                                                let uu____17177 =
                                                  let uu____17178 =
                                                    let uu____17185 =
                                                      let uu____17186 =
                                                        let uu____17197 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17197) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17186 in
                                                    (uu____17185,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17178 in
                                                [uu____17177])
                                       | uu____17214 -> [])) in
                             let uu____17215 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17215 with
                              | (vars,guards,env',decls1,uu____17242) ->
                                  let uu____17255 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17264 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17264, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17266 =
                                          encode_formula p env' in
                                        (match uu____17266 with
                                         | (g,ds) ->
                                             let uu____17277 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17277,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17255 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17290 =
                                           let uu____17297 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17297) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17290 in
                                       let uu____17306 =
                                         let vname_decl =
                                           let uu____17314 =
                                             let uu____17325 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17335  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17325,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17314 in
                                         let uu____17344 =
                                           let env2 =
                                             let uu___403_17350 = env1 in
                                             {
                                               bindings =
                                                 (uu___403_17350.bindings);
                                               depth = (uu___403_17350.depth);
                                               tcenv = (uu___403_17350.tcenv);
                                               warn = (uu___403_17350.warn);
                                               cache = (uu___403_17350.cache);
                                               nolabels =
                                                 (uu___403_17350.nolabels);
                                               use_zfuel_name =
                                                 (uu___403_17350.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___403_17350.current_module_name)
                                             } in
                                           let uu____17351 =
                                             let uu____17352 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17352 in
                                           if uu____17351
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17344 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17367::uu____17368 ->
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
                                                     let uu____17408 =
                                                       let uu____17419 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17419) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17408 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17446 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17449 =
                                               match formals with
                                               | [] ->
                                                   let uu____17466 =
                                                     let uu____17467 =
                                                       let uu____17470 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17470 in
                                                     push_free_var env1 lid
                                                       vname uu____17467 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17466)
                                               | uu____17475 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17482 =
                                                       let uu____17489 =
                                                         let uu____17490 =
                                                           let uu____17501 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17501) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17490 in
                                                       (uu____17489,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17482 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17449 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17306 with
                                        | (decls2,env2) ->
                                            let uu____17544 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17552 =
                                                encode_term res_t1 env' in
                                              match uu____17552 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17565 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17565, decls) in
                                            (match uu____17544 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17576 =
                                                     let uu____17583 =
                                                       let uu____17584 =
                                                         let uu____17595 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17595) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17584 in
                                                     (uu____17583,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17576 in
                                                 let freshness =
                                                   let uu____17611 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17611
                                                   then
                                                     let uu____17616 =
                                                       let uu____17617 =
                                                         let uu____17628 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17639 =
                                                           varops.next_id () in
                                                         (vname, uu____17628,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17639) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17617 in
                                                     let uu____17642 =
                                                       let uu____17645 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17645] in
                                                     uu____17616 ::
                                                       uu____17642
                                                   else [] in
                                                 let g =
                                                   let uu____17650 =
                                                     let uu____17653 =
                                                       let uu____17656 =
                                                         let uu____17659 =
                                                           let uu____17662 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17662 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17659 in
                                                       FStar_List.append
                                                         decls3 uu____17656 in
                                                     FStar_List.append decls2
                                                       uu____17653 in
                                                   FStar_List.append decls11
                                                     uu____17650 in
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
          let uu____17693 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17693 with
          | FStar_Pervasives_Native.None  ->
              let uu____17730 = encode_free_var false env x t t_norm [] in
              (match uu____17730 with
               | (decls,env1) ->
                   let uu____17757 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17757 with
                    | (n1,x',uu____17784) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17805) ->
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
            let uu____17860 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17860 with
            | (decls,env1) ->
                let uu____17879 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17879
                then
                  let uu____17886 =
                    let uu____17889 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17889 in
                  (uu____17886, env1)
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
             (fun uu____17941  ->
                fun lb  ->
                  match uu____17941 with
                  | (decls,env1) ->
                      let uu____17961 =
                        let uu____17968 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17968
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17961 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____17989 = FStar_Syntax_Util.head_and_args t in
    match uu____17989 with
    | (hd1,args) ->
        let uu____18026 =
          let uu____18027 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18027.FStar_Syntax_Syntax.n in
        (match uu____18026 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18031,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18050 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18072  ->
      fun quals  ->
        match uu____18072 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18148 = FStar_Util.first_N nbinders formals in
              match uu____18148 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18229  ->
                         fun uu____18230  ->
                           match (uu____18229, uu____18230) with
                           | ((formal,uu____18248),(binder,uu____18250)) ->
                               let uu____18259 =
                                 let uu____18266 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18266) in
                               FStar_Syntax_Syntax.NT uu____18259) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18274 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18305  ->
                              match uu____18305 with
                              | (x,i) ->
                                  let uu____18316 =
                                    let uu___404_18317 = x in
                                    let uu____18318 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_18317.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_18317.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18318
                                    } in
                                  (uu____18316, i))) in
                    FStar_All.pipe_right uu____18274
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18336 =
                      let uu____18337 = FStar_Syntax_Subst.compress body in
                      let uu____18338 =
                        let uu____18339 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18339 in
                      FStar_Syntax_Syntax.extend_app_n uu____18337
                        uu____18338 in
                    uu____18336 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18400 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18400
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___405_18403 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___405_18403.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___405_18403.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___405_18403.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___405_18403.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___405_18403.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___405_18403.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___405_18403.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___405_18403.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___405_18403.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___405_18403.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___405_18403.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___405_18403.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___405_18403.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___405_18403.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___405_18403.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___405_18403.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___405_18403.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___405_18403.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___405_18403.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___405_18403.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___405_18403.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___405_18403.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___405_18403.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___405_18403.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___405_18403.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___405_18403.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___405_18403.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___405_18403.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___405_18403.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___405_18403.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___405_18403.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___405_18403.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___405_18403.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18436 = FStar_Syntax_Util.abs_formals e in
                match uu____18436 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18500::uu____18501 ->
                         let uu____18516 =
                           let uu____18517 =
                             let uu____18520 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18520 in
                           uu____18517.FStar_Syntax_Syntax.n in
                         (match uu____18516 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18563 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18563 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18605 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18605
                                   then
                                     let uu____18640 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18640 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18734  ->
                                                   fun uu____18735  ->
                                                     match (uu____18734,
                                                             uu____18735)
                                                     with
                                                     | ((x,uu____18753),
                                                        (b,uu____18755)) ->
                                                         let uu____18764 =
                                                           let uu____18771 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18771) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18764)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18773 =
                                            let uu____18794 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18794) in
                                          (uu____18773, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18862 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18862 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18951) ->
                              let uu____18956 =
                                let uu____18977 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18977 in
                              (uu____18956, true)
                          | uu____19042 when Prims.op_Negation norm1 ->
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
                          | uu____19044 ->
                              let uu____19045 =
                                let uu____19046 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19047 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19046
                                  uu____19047 in
                              failwith uu____19045)
                     | uu____19072 ->
                         let rec aux' t_norm2 =
                           let uu____19097 =
                             let uu____19098 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19098.FStar_Syntax_Syntax.n in
                           match uu____19097 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19139 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19139 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19167 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19167 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19247)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19252 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19308 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19308
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19320 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19414  ->
                            fun lb  ->
                              match uu____19414 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19509 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19509
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19512 =
                                      let uu____19527 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19527
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19512 with
                                    | (tok,decl,env2) ->
                                        let uu____19573 =
                                          let uu____19586 =
                                            let uu____19597 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19597, tok) in
                                          uu____19586 :: toks in
                                        (uu____19573, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19320 with
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
                        | uu____19780 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19788 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19788 vars)
                            else
                              (let uu____19790 =
                                 let uu____19797 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19797) in
                               FStar_SMTEncoding_Util.mkApp uu____19790) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19879;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19881;
                             FStar_Syntax_Syntax.lbeff = uu____19882;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19945 =
                              let uu____19952 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19952 with
                              | (tcenv',uu____19970,e_t) ->
                                  let uu____19976 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19987 -> failwith "Impossible" in
                                  (match uu____19976 with
                                   | (e1,t_norm1) ->
                                       ((let uu___408_20003 = env2 in
                                         {
                                           bindings =
                                             (uu___408_20003.bindings);
                                           depth = (uu___408_20003.depth);
                                           tcenv = tcenv';
                                           warn = (uu___408_20003.warn);
                                           cache = (uu___408_20003.cache);
                                           nolabels =
                                             (uu___408_20003.nolabels);
                                           use_zfuel_name =
                                             (uu___408_20003.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___408_20003.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___408_20003.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19945 with
                             | (env',e1,t_norm1) ->
                                 let uu____20013 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20013 with
                                  | ((binders,body,uu____20034,uu____20035),curry)
                                      ->
                                      ((let uu____20046 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20046
                                        then
                                          let uu____20047 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20048 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20047 uu____20048
                                        else ());
                                       (let uu____20050 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20050 with
                                        | (vars,guards,env'1,binder_decls,uu____20077)
                                            ->
                                            let body1 =
                                              let uu____20091 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20091
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20094 =
                                              let uu____20103 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20103
                                              then
                                                let uu____20114 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20115 =
                                                  encode_formula body1 env'1 in
                                                (uu____20114, uu____20115)
                                              else
                                                (let uu____20125 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20125)) in
                                            (match uu____20094 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20148 =
                                                     let uu____20155 =
                                                       let uu____20156 =
                                                         let uu____20167 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20167) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20156 in
                                                     let uu____20178 =
                                                       let uu____20181 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20181 in
                                                     (uu____20155,
                                                       uu____20178,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20148 in
                                                 let uu____20184 =
                                                   let uu____20187 =
                                                     let uu____20190 =
                                                       let uu____20193 =
                                                         let uu____20196 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20196 in
                                                       FStar_List.append
                                                         decls2 uu____20193 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20190 in
                                                   FStar_List.append decls1
                                                     uu____20187 in
                                                 (uu____20184, env2))))))
                        | uu____20201 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20286 = varops.fresh "fuel" in
                          (uu____20286, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20289 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20377  ->
                                  fun uu____20378  ->
                                    match (uu____20377, uu____20378) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20526 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20526 in
                                        let gtok =
                                          let uu____20528 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20528 in
                                        let env4 =
                                          let uu____20530 =
                                            let uu____20533 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20533 in
                                          push_free_var env3 flid gtok
                                            uu____20530 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20289 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20689 t_norm
                              uu____20691 =
                              match (uu____20689, uu____20691) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20735;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20736;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20764 =
                                    let uu____20771 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20771 with
                                    | (tcenv',uu____20793,e_t) ->
                                        let uu____20799 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20810 ->
                                              failwith "Impossible" in
                                        (match uu____20799 with
                                         | (e1,t_norm1) ->
                                             ((let uu___409_20826 = env3 in
                                               {
                                                 bindings =
                                                   (uu___409_20826.bindings);
                                                 depth =
                                                   (uu___409_20826.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___409_20826.warn);
                                                 cache =
                                                   (uu___409_20826.cache);
                                                 nolabels =
                                                   (uu___409_20826.nolabels);
                                                 use_zfuel_name =
                                                   (uu___409_20826.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___409_20826.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___409_20826.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20764 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20841 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20841
                                         then
                                           let uu____20842 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20843 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20844 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20842 uu____20843
                                             uu____20844
                                         else ());
                                        (let uu____20846 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20846 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20883 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20883
                                               then
                                                 let uu____20884 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20885 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20886 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20887 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20884 uu____20885
                                                   uu____20886 uu____20887
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20891 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20891 with
                                               | (vars,guards,env'1,binder_decls,uu____20922)
                                                   ->
                                                   let decl_g =
                                                     let uu____20936 =
                                                       let uu____20947 =
                                                         let uu____20950 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20950 in
                                                       (g, uu____20947,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20936 in
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
                                                     let uu____20975 =
                                                       let uu____20982 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20982) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20975 in
                                                   let gsapp =
                                                     let uu____20992 =
                                                       let uu____20999 =
                                                         let uu____21002 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21002 ::
                                                           vars_tm in
                                                       (g, uu____20999) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20992 in
                                                   let gmax =
                                                     let uu____21008 =
                                                       let uu____21015 =
                                                         let uu____21018 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21018 ::
                                                           vars_tm in
                                                       (g, uu____21015) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21008 in
                                                   let body1 =
                                                     let uu____21024 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21024
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21026 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21026 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21044 =
                                                            let uu____21051 =
                                                              let uu____21052
                                                                =
                                                                let uu____21067
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
                                                                  uu____21067) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21052 in
                                                            let uu____21088 =
                                                              let uu____21091
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21091 in
                                                            (uu____21051,
                                                              uu____21088,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21044 in
                                                        let eqn_f =
                                                          let uu____21095 =
                                                            let uu____21102 =
                                                              let uu____21103
                                                                =
                                                                let uu____21114
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21114) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21103 in
                                                            (uu____21102,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21095 in
                                                        let eqn_g' =
                                                          let uu____21128 =
                                                            let uu____21135 =
                                                              let uu____21136
                                                                =
                                                                let uu____21147
                                                                  =
                                                                  let uu____21148
                                                                    =
                                                                    let uu____21153
                                                                    =
                                                                    let uu____21154
                                                                    =
                                                                    let uu____21161
                                                                    =
                                                                    let uu____21164
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21164
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21161) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21154 in
                                                                    (gsapp,
                                                                    uu____21153) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21148 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21147) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21136 in
                                                            (uu____21135,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21128 in
                                                        let uu____21187 =
                                                          let uu____21196 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21196
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21225)
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
                                                                  let uu____21250
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21250
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21255
                                                                  =
                                                                  let uu____21262
                                                                    =
                                                                    let uu____21263
                                                                    =
                                                                    let uu____21274
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21274) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21263 in
                                                                  (uu____21262,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21255 in
                                                              let uu____21295
                                                                =
                                                                let uu____21302
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21302
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21315
                                                                    =
                                                                    let uu____21318
                                                                    =
                                                                    let uu____21319
                                                                    =
                                                                    let uu____21326
                                                                    =
                                                                    let uu____21327
                                                                    =
                                                                    let uu____21338
                                                                    =
                                                                    let uu____21339
                                                                    =
                                                                    let uu____21344
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21344,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21339 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21338) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21327 in
                                                                    (uu____21326,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21319 in
                                                                    [uu____21318] in
                                                                    (d3,
                                                                    uu____21315) in
                                                              (match uu____21295
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21187
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
                            let uu____21409 =
                              let uu____21422 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21501  ->
                                   fun uu____21502  ->
                                     match (uu____21501, uu____21502) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21657 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21657 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21422 in
                            (match uu____21409 with
                             | (decls2,eqns,env01) ->
                                 let uu____21730 =
                                   let isDeclFun uu___375_21742 =
                                     match uu___375_21742 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21743 -> true
                                     | uu____21754 -> false in
                                   let uu____21755 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21755
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21730 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21795 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___376_21799  ->
                                 match uu___376_21799 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21800 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21806 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21806))) in
                      if uu____21795
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
                   let uu____21858 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21858
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
        let uu____21907 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21907 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21911 = encode_sigelt' env se in
      match uu____21911 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21927 =
                  let uu____21928 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21928 in
                [uu____21927]
            | uu____21929 ->
                let uu____21930 =
                  let uu____21933 =
                    let uu____21934 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21934 in
                  uu____21933 :: g in
                let uu____21935 =
                  let uu____21938 =
                    let uu____21939 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21939 in
                  [uu____21938] in
                FStar_List.append uu____21930 uu____21935 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21952 =
          let uu____21953 = FStar_Syntax_Subst.compress t in
          uu____21953.FStar_Syntax_Syntax.n in
        match uu____21952 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21957)) -> s = "opaque_to_smt"
        | uu____21958 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21963 =
          let uu____21964 = FStar_Syntax_Subst.compress t in
          uu____21964.FStar_Syntax_Syntax.n in
        match uu____21963 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21968)) -> s = "uninterpreted_by_smt"
        | uu____21969 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21974 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21979 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21982 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21985 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22000 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22004 =
            let uu____22005 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22005 Prims.op_Negation in
          if uu____22004
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22031 ->
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
               let uu____22051 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22051 with
               | (aname,atok,env2) ->
                   let uu____22067 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22067 with
                    | (formals,uu____22085) ->
                        let uu____22098 =
                          let uu____22103 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22103 env2 in
                        (match uu____22098 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22115 =
                                 let uu____22116 =
                                   let uu____22127 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22143  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22127,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22116 in
                               [uu____22115;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22156 =
                               let aux uu____22208 uu____22209 =
                                 match (uu____22208, uu____22209) with
                                 | ((bv,uu____22261),(env3,acc_sorts,acc)) ->
                                     let uu____22299 = gen_term_var env3 bv in
                                     (match uu____22299 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22156 with
                              | (uu____22371,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22394 =
                                      let uu____22401 =
                                        let uu____22402 =
                                          let uu____22413 =
                                            let uu____22414 =
                                              let uu____22419 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22419) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22414 in
                                          ([[app]], xs_sorts, uu____22413) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22402 in
                                      (uu____22401,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22394 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22439 =
                                      let uu____22446 =
                                        let uu____22447 =
                                          let uu____22458 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22458) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22447 in
                                      (uu____22446,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22439 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22477 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22477 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22505,uu____22506)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22507 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22507 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22524,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22530 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___377_22534  ->
                      match uu___377_22534 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22535 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22540 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22541 -> false)) in
            Prims.op_Negation uu____22530 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22550 =
               let uu____22557 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22557 env fv t quals in
             match uu____22550 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22572 =
                   let uu____22575 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22575 in
                 (uu____22572, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22583 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22583 with
           | (uu____22592,f1) ->
               let uu____22594 = encode_formula f1 env in
               (match uu____22594 with
                | (f2,decls) ->
                    let g =
                      let uu____22608 =
                        let uu____22609 =
                          let uu____22616 =
                            let uu____22619 =
                              let uu____22620 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22620 in
                            FStar_Pervasives_Native.Some uu____22619 in
                          let uu____22621 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22616, uu____22621) in
                        FStar_SMTEncoding_Util.mkAssume uu____22609 in
                      [uu____22608] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22627) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22639 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22657 =
                       let uu____22660 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22660.FStar_Syntax_Syntax.fv_name in
                     uu____22657.FStar_Syntax_Syntax.v in
                   let uu____22661 =
                     let uu____22662 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22662 in
                   if uu____22661
                   then
                     let val_decl =
                       let uu___412_22690 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___412_22690.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___412_22690.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___412_22690.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22695 = encode_sigelt' env1 val_decl in
                     match uu____22695 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22639 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22723,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22725;
                          FStar_Syntax_Syntax.lbtyp = uu____22726;
                          FStar_Syntax_Syntax.lbeff = uu____22727;
                          FStar_Syntax_Syntax.lbdef = uu____22728;_}::[]),uu____22729)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22748 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22748 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22777 =
                   let uu____22780 =
                     let uu____22781 =
                       let uu____22788 =
                         let uu____22789 =
                           let uu____22800 =
                             let uu____22801 =
                               let uu____22806 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22806) in
                             FStar_SMTEncoding_Util.mkEq uu____22801 in
                           ([[b2t_x]], [xx], uu____22800) in
                         FStar_SMTEncoding_Util.mkForall uu____22789 in
                       (uu____22788,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22781 in
                   [uu____22780] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22777 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22839,uu____22840) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___378_22849  ->
                  match uu___378_22849 with
                  | FStar_Syntax_Syntax.Discriminator uu____22850 -> true
                  | uu____22851 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22854,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22865 =
                     let uu____22866 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22866.FStar_Ident.idText in
                   uu____22865 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___379_22870  ->
                     match uu___379_22870 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22871 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22875) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___380_22892  ->
                  match uu___380_22892 with
                  | FStar_Syntax_Syntax.Projector uu____22893 -> true
                  | uu____22898 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22901 = try_lookup_free_var env l in
          (match uu____22901 with
           | FStar_Pervasives_Native.Some uu____22908 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___413_22912 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___413_22912.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___413_22912.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___413_22912.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22919) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22937) ->
          let uu____22946 = encode_sigelts env ses in
          (match uu____22946 with
           | (g,env1) ->
               let uu____22963 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___381_22986  ->
                         match uu___381_22986 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22987;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22988;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22989;_}
                             -> false
                         | uu____22992 -> true)) in
               (match uu____22963 with
                | (g',inversions) ->
                    let uu____23007 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___382_23028  ->
                              match uu___382_23028 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23029 ->
                                  true
                              | uu____23040 -> false)) in
                    (match uu____23007 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23058,tps,k,uu____23061,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___383_23078  ->
                    match uu___383_23078 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23079 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23088 = c in
              match uu____23088 with
              | (name,args,uu____23093,uu____23094,uu____23095) ->
                  let uu____23100 =
                    let uu____23101 =
                      let uu____23112 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23129  ->
                                match uu____23129 with
                                | (uu____23136,sort,uu____23138) -> sort)) in
                      (name, uu____23112, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23101 in
                  [uu____23100]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23165 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23171 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23171 FStar_Option.isNone)) in
            if uu____23165
            then []
            else
              (let uu____23203 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23203 with
               | (xxsym,xx) ->
                   let uu____23212 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23251  ->
                             fun l  ->
                               match uu____23251 with
                               | (out,decls) ->
                                   let uu____23271 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23271 with
                                    | (uu____23282,data_t) ->
                                        let uu____23284 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23284 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23330 =
                                                 let uu____23331 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23331.FStar_Syntax_Syntax.n in
                                               match uu____23330 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23342,indices) ->
                                                   indices
                                               | uu____23364 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23388  ->
                                                         match uu____23388
                                                         with
                                                         | (x,uu____23394) ->
                                                             let uu____23395
                                                               =
                                                               let uu____23396
                                                                 =
                                                                 let uu____23403
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23403,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23396 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23395)
                                                    env) in
                                             let uu____23406 =
                                               encode_args indices env1 in
                                             (match uu____23406 with
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
                                                      let uu____23432 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23448
                                                                 =
                                                                 let uu____23453
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23453,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23448)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23432
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23456 =
                                                      let uu____23457 =
                                                        let uu____23462 =
                                                          let uu____23463 =
                                                            let uu____23468 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23468,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23463 in
                                                        (out, uu____23462) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23457 in
                                                    (uu____23456,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23212 with
                    | (data_ax,decls) ->
                        let uu____23481 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23481 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23492 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23492 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23496 =
                                 let uu____23503 =
                                   let uu____23504 =
                                     let uu____23515 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23530 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23515,
                                       uu____23530) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23504 in
                                 let uu____23545 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23503,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23545) in
                               FStar_SMTEncoding_Util.mkAssume uu____23496 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23548 =
            let uu____23561 =
              let uu____23562 = FStar_Syntax_Subst.compress k in
              uu____23562.FStar_Syntax_Syntax.n in
            match uu____23561 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23607 -> (tps, k) in
          (match uu____23548 with
           | (formals,res) ->
               let uu____23630 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23630 with
                | (formals1,res1) ->
                    let uu____23641 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23641 with
                     | (vars,guards,env',binder_decls,uu____23666) ->
                         let uu____23679 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23679 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23698 =
                                  let uu____23705 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23705) in
                                FStar_SMTEncoding_Util.mkApp uu____23698 in
                              let uu____23714 =
                                let tname_decl =
                                  let uu____23724 =
                                    let uu____23725 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23757  ->
                                              match uu____23757 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23770 = varops.next_id () in
                                    (tname, uu____23725,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23770, false) in
                                  constructor_or_logic_type_decl uu____23724 in
                                let uu____23779 =
                                  match vars with
                                  | [] ->
                                      let uu____23792 =
                                        let uu____23793 =
                                          let uu____23796 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23796 in
                                        push_free_var env1 t tname
                                          uu____23793 in
                                      ([], uu____23792)
                                  | uu____23803 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23812 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23812 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23826 =
                                          let uu____23833 =
                                            let uu____23834 =
                                              let uu____23849 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23849) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23834 in
                                          (uu____23833,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23826 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23779 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23714 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23889 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23889 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23907 =
                                               let uu____23908 =
                                                 let uu____23915 =
                                                   let uu____23916 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23916 in
                                                 (uu____23915,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23908 in
                                             [uu____23907]
                                           else [] in
                                         let uu____23920 =
                                           let uu____23923 =
                                             let uu____23926 =
                                               let uu____23927 =
                                                 let uu____23934 =
                                                   let uu____23935 =
                                                     let uu____23946 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23946) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23935 in
                                                 (uu____23934,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23927 in
                                             [uu____23926] in
                                           FStar_List.append karr uu____23923 in
                                         FStar_List.append decls1 uu____23920 in
                                   let aux =
                                     let uu____23962 =
                                       let uu____23965 =
                                         inversion_axioms tapp vars in
                                       let uu____23968 =
                                         let uu____23971 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23971] in
                                       FStar_List.append uu____23965
                                         uu____23968 in
                                     FStar_List.append kindingAx uu____23962 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23978,uu____23979,uu____23980,uu____23981,uu____23982)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23990,t,uu____23992,n_tps,uu____23994) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24002 = new_term_constant_and_tok_from_lid env d in
          (match uu____24002 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24019 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24019 with
                | (formals,t_res) ->
                    let uu____24054 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24054 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24068 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24068 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24138 =
                                            mk_term_projector_name d x in
                                          (uu____24138,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24140 =
                                  let uu____24159 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24159, true) in
                                FStar_All.pipe_right uu____24140
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
                              let uu____24198 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24198 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24210::uu____24211 ->
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
                                         let uu____24256 =
                                           let uu____24267 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24267) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24256
                                     | uu____24292 -> tok_typing in
                                   let uu____24301 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24301 with
                                    | (vars',guards',env'',decls_formals,uu____24326)
                                        ->
                                        let uu____24339 =
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
                                        (match uu____24339 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24370 ->
                                                   let uu____24377 =
                                                     let uu____24378 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24378 in
                                                   [uu____24377] in
                                             let encode_elim uu____24388 =
                                               let uu____24389 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24389 with
                                               | (head1,args) ->
                                                   let uu____24432 =
                                                     let uu____24433 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24433.FStar_Syntax_Syntax.n in
                                                   (match uu____24432 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24443;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24444;_},uu____24445)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24451 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24451
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
                                                                 | uu____24494
                                                                    ->
                                                                    let uu____24495
                                                                    =
                                                                    let uu____24496
                                                                    =
                                                                    let uu____24501
                                                                    =
                                                                    let uu____24502
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24502 in
                                                                    (uu____24501,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24496 in
                                                                    FStar_Exn.raise
                                                                    uu____24495 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24518
                                                                    =
                                                                    let uu____24519
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24519 in
                                                                    if
                                                                    uu____24518
                                                                    then
                                                                    let uu____24532
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____24532]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____24534
                                                               =
                                                               let uu____24547
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24597
                                                                     ->
                                                                    fun
                                                                    uu____24598
                                                                     ->
                                                                    match 
                                                                    (uu____24597,
                                                                    uu____24598)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24693
                                                                    =
                                                                    let uu____24700
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24700 in
                                                                    (match uu____24693
                                                                    with
                                                                    | 
                                                                    (uu____24713,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24721
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____24721
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24723
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____24723
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
                                                                 uu____24547 in
                                                             (match uu____24534
                                                              with
                                                              | (uu____24738,arg_vars,elim_eqns_or_guards,uu____24741)
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
                                                                    let uu____24771
                                                                    =
                                                                    let uu____24778
                                                                    =
                                                                    let uu____24779
                                                                    =
                                                                    let uu____24790
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24801
                                                                    =
                                                                    let uu____24802
                                                                    =
                                                                    let uu____24807
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____24807) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24802 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24790,
                                                                    uu____24801) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24779 in
                                                                    (uu____24778,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24771 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24830
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____24830,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____24832
                                                                    =
                                                                    let uu____24839
                                                                    =
                                                                    let uu____24840
                                                                    =
                                                                    let uu____24851
                                                                    =
                                                                    let uu____24856
                                                                    =
                                                                    let uu____24859
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____24859] in
                                                                    [uu____24856] in
                                                                    let uu____24864
                                                                    =
                                                                    let uu____24865
                                                                    =
                                                                    let uu____24870
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____24871
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____24870,
                                                                    uu____24871) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24865 in
                                                                    (uu____24851,
                                                                    [x],
                                                                    uu____24864) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24840 in
                                                                    let uu____24890
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____24839,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____24890) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24832
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____24897
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
                                                                    (let uu____24925
                                                                    =
                                                                    let uu____24926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____24926
                                                                    dapp1 in
                                                                    [uu____24925]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____24897
                                                                    FStar_List.flatten in
                                                                    let uu____24933
                                                                    =
                                                                    let uu____24940
                                                                    =
                                                                    let uu____24941
                                                                    =
                                                                    let uu____24952
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____24963
                                                                    =
                                                                    let uu____24964
                                                                    =
                                                                    let uu____24969
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____24969) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24964 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24952,
                                                                    uu____24963) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24941 in
                                                                    (uu____24940,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24933) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24990 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24990
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
                                                                 | uu____25033
                                                                    ->
                                                                    let uu____25034
                                                                    =
                                                                    let uu____25035
                                                                    =
                                                                    let uu____25040
                                                                    =
                                                                    let uu____25041
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25041 in
                                                                    (uu____25040,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25035 in
                                                                    FStar_Exn.raise
                                                                    uu____25034 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25057
                                                                    =
                                                                    let uu____25058
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25058 in
                                                                    if
                                                                    uu____25057
                                                                    then
                                                                    let uu____25071
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25071]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25073
                                                               =
                                                               let uu____25086
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25136
                                                                     ->
                                                                    fun
                                                                    uu____25137
                                                                     ->
                                                                    match 
                                                                    (uu____25136,
                                                                    uu____25137)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25232
                                                                    =
                                                                    let uu____25239
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25239 in
                                                                    (match uu____25232
                                                                    with
                                                                    | 
                                                                    (uu____25252,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25260
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25260
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25262
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25262
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
                                                                 uu____25086 in
                                                             (match uu____25073
                                                              with
                                                              | (uu____25277,arg_vars,elim_eqns_or_guards,uu____25280)
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
                                                                    let uu____25310
                                                                    =
                                                                    let uu____25317
                                                                    =
                                                                    let uu____25318
                                                                    =
                                                                    let uu____25329
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25340
                                                                    =
                                                                    let uu____25341
                                                                    =
                                                                    let uu____25346
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25346) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25341 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25329,
                                                                    uu____25340) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25318 in
                                                                    (uu____25317,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25310 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25369
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25369,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25371
                                                                    =
                                                                    let uu____25378
                                                                    =
                                                                    let uu____25379
                                                                    =
                                                                    let uu____25390
                                                                    =
                                                                    let uu____25395
                                                                    =
                                                                    let uu____25398
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25398] in
                                                                    [uu____25395] in
                                                                    let uu____25403
                                                                    =
                                                                    let uu____25404
                                                                    =
                                                                    let uu____25409
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25410
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25409,
                                                                    uu____25410) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25404 in
                                                                    (uu____25390,
                                                                    [x],
                                                                    uu____25403) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25379 in
                                                                    let uu____25429
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25378,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25429) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25371
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25436
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
                                                                    (let uu____25464
                                                                    =
                                                                    let uu____25465
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25465
                                                                    dapp1 in
                                                                    [uu____25464]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25436
                                                                    FStar_List.flatten in
                                                                    let uu____25472
                                                                    =
                                                                    let uu____25479
                                                                    =
                                                                    let uu____25480
                                                                    =
                                                                    let uu____25491
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25502
                                                                    =
                                                                    let uu____25503
                                                                    =
                                                                    let uu____25508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25508) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25503 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25491,
                                                                    uu____25502) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25480 in
                                                                    (uu____25479,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25472) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25527 ->
                                                        ((let uu____25529 =
                                                            let uu____25530 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25531 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25530
                                                              uu____25531 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25529);
                                                         ([], []))) in
                                             let uu____25536 = encode_elim () in
                                             (match uu____25536 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25556 =
                                                      let uu____25559 =
                                                        let uu____25562 =
                                                          let uu____25565 =
                                                            let uu____25568 =
                                                              let uu____25569
                                                                =
                                                                let uu____25580
                                                                  =
                                                                  let uu____25583
                                                                    =
                                                                    let uu____25584
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25584 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25583 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25580) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25569 in
                                                            [uu____25568] in
                                                          let uu____25589 =
                                                            let uu____25592 =
                                                              let uu____25595
                                                                =
                                                                let uu____25598
                                                                  =
                                                                  let uu____25601
                                                                    =
                                                                    let uu____25604
                                                                    =
                                                                    let uu____25607
                                                                    =
                                                                    let uu____25608
                                                                    =
                                                                    let uu____25615
                                                                    =
                                                                    let uu____25616
                                                                    =
                                                                    let uu____25627
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25627) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25616 in
                                                                    (uu____25615,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25608 in
                                                                    let uu____25640
                                                                    =
                                                                    let uu____25643
                                                                    =
                                                                    let uu____25644
                                                                    =
                                                                    let uu____25651
                                                                    =
                                                                    let uu____25652
                                                                    =
                                                                    let uu____25663
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25674
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25663,
                                                                    uu____25674) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25652 in
                                                                    (uu____25651,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25644 in
                                                                    [uu____25643] in
                                                                    uu____25607
                                                                    ::
                                                                    uu____25640 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25604 in
                                                                  FStar_List.append
                                                                    uu____25601
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25598 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25595 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25592 in
                                                          FStar_List.append
                                                            uu____25565
                                                            uu____25589 in
                                                        FStar_List.append
                                                          decls3 uu____25562 in
                                                      FStar_List.append
                                                        decls2 uu____25559 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25556 in
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
           (fun uu____25720  ->
              fun se  ->
                match uu____25720 with
                | (g,env1) ->
                    let uu____25740 = encode_sigelt env1 se in
                    (match uu____25740 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25797 =
        match uu____25797 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25829 ->
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
                 ((let uu____25835 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25835
                   then
                     let uu____25836 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25837 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25838 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25836 uu____25837 uu____25838
                   else ());
                  (let uu____25840 = encode_term t1 env1 in
                   match uu____25840 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25856 =
                         let uu____25863 =
                           let uu____25864 =
                             let uu____25865 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25865
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25864 in
                         new_term_constant_from_string env1 x uu____25863 in
                       (match uu____25856 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25881 = FStar_Options.log_queries () in
                              if uu____25881
                              then
                                let uu____25884 =
                                  let uu____25885 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25886 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25887 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25885 uu____25886 uu____25887 in
                                FStar_Pervasives_Native.Some uu____25884
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25903,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25917 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25917 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25940,se,uu____25942) ->
                 let uu____25947 = encode_sigelt env1 se in
                 (match uu____25947 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25964,se) ->
                 let uu____25970 = encode_sigelt env1 se in
                 (match uu____25970 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25987 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25987 with | (uu____26010,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26022 'Auu____26023 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26023,'Auu____26022)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26091  ->
              match uu____26091 with
              | (l,uu____26103,uu____26104) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26150  ->
              match uu____26150 with
              | (l,uu____26164,uu____26165) ->
                  let uu____26174 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26175 =
                    let uu____26178 =
                      let uu____26179 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26179 in
                    [uu____26178] in
                  uu____26174 :: uu____26175)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26200 =
      let uu____26203 =
        let uu____26204 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26207 =
          let uu____26208 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26208 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26204;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26207
        } in
      [uu____26203] in
    FStar_ST.op_Colon_Equals last_env uu____26200
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26265 = FStar_ST.op_Bang last_env in
      match uu____26265 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26319 ->
          let uu___414_26322 = e in
          let uu____26323 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___414_26322.bindings);
            depth = (uu___414_26322.depth);
            tcenv;
            warn = (uu___414_26322.warn);
            cache = (uu___414_26322.cache);
            nolabels = (uu___414_26322.nolabels);
            use_zfuel_name = (uu___414_26322.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___414_26322.encode_non_total_function_typ);
            current_module_name = uu____26323
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26327 = FStar_ST.op_Bang last_env in
    match uu____26327 with
    | [] -> failwith "Empty env stack"
    | uu____26380::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26436  ->
    let uu____26437 = FStar_ST.op_Bang last_env in
    match uu____26437 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___415_26498 = hd1 in
          {
            bindings = (uu___415_26498.bindings);
            depth = (uu___415_26498.depth);
            tcenv = (uu___415_26498.tcenv);
            warn = (uu___415_26498.warn);
            cache = refs;
            nolabels = (uu___415_26498.nolabels);
            use_zfuel_name = (uu___415_26498.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___415_26498.encode_non_total_function_typ);
            current_module_name = (uu___415_26498.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26551  ->
    let uu____26552 = FStar_ST.op_Bang last_env in
    match uu____26552 with
    | [] -> failwith "Popping an empty stack"
    | uu____26605::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26696::uu____26697,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___416_26705 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___416_26705.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___416_26705.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___416_26705.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26706 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26721 =
        let uu____26724 =
          let uu____26725 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26725 in
        let uu____26726 = open_fact_db_tags env in uu____26724 :: uu____26726 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26721
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
      let uu____26748 = encode_sigelt env se in
      match uu____26748 with
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
        let uu____26784 = FStar_Options.log_queries () in
        if uu____26784
        then
          let uu____26787 =
            let uu____26788 =
              let uu____26789 =
                let uu____26790 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26790 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26789 in
            FStar_SMTEncoding_Term.Caption uu____26788 in
          uu____26787 :: decls
        else decls in
      (let uu____26801 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26801
       then
         let uu____26802 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26802
       else ());
      (let env =
         let uu____26805 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26805 tcenv in
       let uu____26806 = encode_top_level_facts env se in
       match uu____26806 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26820 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26820)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26832 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26832
       then
         let uu____26833 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26833
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26868  ->
                 fun se  ->
                   match uu____26868 with
                   | (g,env2) ->
                       let uu____26888 = encode_top_level_facts env2 se in
                       (match uu____26888 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26911 =
         encode_signature
           (let uu___417_26920 = env in
            {
              bindings = (uu___417_26920.bindings);
              depth = (uu___417_26920.depth);
              tcenv = (uu___417_26920.tcenv);
              warn = false;
              cache = (uu___417_26920.cache);
              nolabels = (uu___417_26920.nolabels);
              use_zfuel_name = (uu___417_26920.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___417_26920.encode_non_total_function_typ);
              current_module_name = (uu___417_26920.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26911 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26937 = FStar_Options.log_queries () in
             if uu____26937
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___418_26945 = env1 in
               {
                 bindings = (uu___418_26945.bindings);
                 depth = (uu___418_26945.depth);
                 tcenv = (uu___418_26945.tcenv);
                 warn = true;
                 cache = (uu___418_26945.cache);
                 nolabels = (uu___418_26945.nolabels);
                 use_zfuel_name = (uu___418_26945.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___418_26945.encode_non_total_function_typ);
                 current_module_name = (uu___418_26945.current_module_name)
               });
            (let uu____26947 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26947
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
        (let uu____26999 =
           let uu____27000 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27000.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26999);
        (let env =
           let uu____27002 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27002 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27014 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27049 = aux rest in
                 (match uu____27049 with
                  | (out,rest1) ->
                      let t =
                        let uu____27079 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27079 with
                        | FStar_Pervasives_Native.Some uu____27084 ->
                            let uu____27085 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27085
                              x.FStar_Syntax_Syntax.sort
                        | uu____27086 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27090 =
                        let uu____27093 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___419_27096 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___419_27096.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___419_27096.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27093 :: out in
                      (uu____27090, rest1))
             | uu____27101 -> ([], bindings1) in
           let uu____27108 = aux bindings in
           match uu____27108 with
           | (closing,bindings1) ->
               let uu____27133 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27133, bindings1) in
         match uu____27014 with
         | (q1,bindings1) ->
             let uu____27156 =
               let uu____27161 =
                 FStar_List.filter
                   (fun uu___384_27166  ->
                      match uu___384_27166 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27167 ->
                          false
                      | uu____27174 -> true) bindings1 in
               encode_env_bindings env uu____27161 in
             (match uu____27156 with
              | (env_decls,env1) ->
                  ((let uu____27192 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27192
                    then
                      let uu____27193 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27193
                    else ());
                   (let uu____27195 = encode_formula q1 env1 in
                    match uu____27195 with
                    | (phi,qdecls) ->
                        let uu____27216 =
                          let uu____27221 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27221 phi in
                        (match uu____27216 with
                         | (labels,phi1) ->
                             let uu____27238 = encode_labels labels in
                             (match uu____27238 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27275 =
                                      let uu____27282 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27283 =
                                        varops.mk_unique "@query" in
                                      (uu____27282,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27283) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27275 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))