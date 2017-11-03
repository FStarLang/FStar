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
        let id1 = next_id1 () in
        let f =
          let uu____1320 = FStar_SMTEncoding_Util.mk_String_const id1 in
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
          let uu____4367 =
            let uu____4368 = FStar_SMTEncoding_Util.mkInteger i in
            FStar_SMTEncoding_Term.boxInt uu____4368 in
          (uu____4367, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4389) ->
          let uu____4390 = varops.string_const s in (uu____4390, [])
      | FStar_Const.Const_range uu____4393 ->
          let uu____4394 = FStar_SMTEncoding_Term.mk_Range_const () in
          (uu____4394, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4400 =
            let uu____4401 = FStar_Syntax_Print.const_to_string c1 in
            FStar_Util.format1 "Unhandled constant: %s" uu____4401 in
          failwith uu____4400
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
        (let uu____4430 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4430
         then
           let uu____4431 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4431
         else ());
        (let uu____4433 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4517  ->
                   fun b  ->
                     match uu____4517 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4596 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4612 = gen_term_var env1 x in
                           match uu____4612 with
                           | (xxsym,xx,env') ->
                               let uu____4636 =
                                 let uu____4641 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4641 env1 xx in
                               (match uu____4636 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4596 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4433 with
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
          let uu____4800 = encode_term t env in
          match uu____4800 with
          | (t1,decls) ->
              let uu____4811 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4811, decls)
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
          let uu____4822 = encode_term t env in
          match uu____4822 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4837 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4837, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4839 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4839, decls))
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
        let uu____4845 = encode_args args_e env in
        match uu____4845 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4864 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4873 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4873 in
            let binary arg_tms1 =
              let uu____4886 =
                let uu____4887 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4887 in
              let uu____4888 =
                let uu____4889 =
                  let uu____4890 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4890 in
                FStar_SMTEncoding_Term.unboxInt uu____4889 in
              (uu____4886, uu____4888) in
            let mk_default uu____4896 =
              let uu____4897 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4897 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4948 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4948
              then
                let uu____4949 = let uu____4950 = mk_args ts in op uu____4950 in
                FStar_All.pipe_right uu____4949 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4979 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4979
              then
                let uu____4980 = binary ts in
                match uu____4980 with
                | (t1,t2) ->
                    let uu____4987 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4987
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4991 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4991
                 then
                   let uu____4992 = op (binary ts) in
                   FStar_All.pipe_right uu____4992
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
            let uu____5123 =
              let uu____5132 =
                FStar_List.tryFind
                  (fun uu____5154  ->
                     match uu____5154 with
                     | (l,uu____5164) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5132 FStar_Util.must in
            (match uu____5123 with
             | (uu____5203,op) ->
                 let uu____5213 = op arg_tms in (uu____5213, decls))
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
        let uu____5221 = FStar_List.hd args_e in
        match uu____5221 with
        | (tm_sz,uu____5229) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5239 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5239 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5247 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5247);
                   t_decls) in
            let uu____5248 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5268::(sz_arg,uu____5270)::uu____5271::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5320 =
                    let uu____5323 = FStar_List.tail args_e in
                    FStar_List.tail uu____5323 in
                  let uu____5326 =
                    let uu____5329 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5329 in
                  (uu____5320, uu____5326)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5335::(sz_arg,uu____5337)::uu____5338::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5387 =
                    let uu____5388 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5388 in
                  failwith uu____5387
              | uu____5397 ->
                  let uu____5404 = FStar_List.tail args_e in
                  (uu____5404, FStar_Pervasives_Native.None) in
            (match uu____5248 with
             | (arg_tms,ext_sz) ->
                 let uu____5427 = encode_args arg_tms env in
                 (match uu____5427 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5448 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5457 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5457 in
                      let unary_arith arg_tms2 =
                        let uu____5466 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5466 in
                      let binary arg_tms2 =
                        let uu____5479 =
                          let uu____5480 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5480 in
                        let uu____5481 =
                          let uu____5482 =
                            let uu____5483 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5483 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5482 in
                        (uu____5479, uu____5481) in
                      let binary_arith arg_tms2 =
                        let uu____5498 =
                          let uu____5499 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5499 in
                        let uu____5500 =
                          let uu____5501 =
                            let uu____5502 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5502 in
                          FStar_SMTEncoding_Term.unboxInt uu____5501 in
                        (uu____5498, uu____5500) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5551 =
                          let uu____5552 = mk_args ts in op uu____5552 in
                        FStar_All.pipe_right uu____5551 resBox in
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
                        let uu____5660 =
                          let uu____5663 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5663 in
                        let uu____5665 =
                          let uu____5668 =
                            let uu____5669 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5669 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5668 in
                        mk_bv uu____5660 unary uu____5665 arg_tms2 in
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
                      let uu____5868 =
                        let uu____5877 =
                          FStar_List.tryFind
                            (fun uu____5899  ->
                               match uu____5899 with
                               | (l,uu____5909) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5877 FStar_Util.must in
                      (match uu____5868 with
                       | (uu____5950,op) ->
                           let uu____5960 = op arg_tms1 in
                           (uu____5960, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5971 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5971
       then
         let uu____5972 = FStar_Syntax_Print.tag_of_term t in
         let uu____5973 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5974 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5972 uu____5973
           uu____5974
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5980 ->
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
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6014 =
             let uu____6015 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____6016 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____6017 = FStar_Syntax_Print.term_to_string t0 in
             let uu____6018 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6015
               uu____6016 uu____6017 uu____6018 in
           failwith uu____6014
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6024 =
             let uu____6025 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6025 in
           failwith uu____6024
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6032) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6073;
              FStar_Syntax_Syntax.vars = uu____6074;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6091 = varops.fresh "t" in
             (uu____6091, FStar_SMTEncoding_Term.Term_sort) in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym in
           let decl =
             let uu____6094 =
               let uu____6105 =
                 let uu____6108 = FStar_Util.format1 "alien term (%s)" desc in
                 FStar_Pervasives_Native.Some uu____6108 in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6105) in
             FStar_SMTEncoding_Term.DeclFun uu____6094 in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6116) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6126 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____6126, [])
       | FStar_Syntax_Syntax.Tm_type uu____6129 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6133) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6158 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6158 with
            | (binders1,res) ->
                let uu____6169 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6169
                then
                  let uu____6174 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6174 with
                   | (vars,guards,env',decls,uu____6199) ->
                       let fsym =
                         let uu____6217 = varops.fresh "f" in
                         (uu____6217, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6220 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___394_6229 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___394_6229.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___394_6229.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___394_6229.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___394_6229.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___394_6229.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___394_6229.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___394_6229.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___394_6229.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___394_6229.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___394_6229.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___394_6229.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___394_6229.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___394_6229.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___394_6229.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___394_6229.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___394_6229.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___394_6229.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___394_6229.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___394_6229.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___394_6229.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___394_6229.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___394_6229.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___394_6229.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___394_6229.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___394_6229.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___394_6229.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___394_6229.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___394_6229.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___394_6229.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___394_6229.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___394_6229.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___394_6229.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___394_6229.FStar_TypeChecker_Env.dep_graph)
                            }) res in
                       (match uu____6220 with
                        | (pre_opt,res_t) ->
                            let uu____6240 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6240 with
                             | (res_pred,decls') ->
                                 let uu____6251 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6264 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6264, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6268 =
                                         encode_formula pre env' in
                                       (match uu____6268 with
                                        | (guard,decls0) ->
                                            let uu____6281 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6281, decls0)) in
                                 (match uu____6251 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6293 =
                                          let uu____6304 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6304) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6293 in
                                      let cvars =
                                        let uu____6322 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6322
                                          (FStar_List.filter
                                             (fun uu____6336  ->
                                                match uu____6336 with
                                                | (x,uu____6342) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6361 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6361 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6369 =
                                             let uu____6370 =
                                               let uu____6377 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6377) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6370 in
                                           (uu____6369,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6397 =
                                               let uu____6398 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6398 in
                                             varops.mk_unique uu____6397 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6409 =
                                               FStar_Options.log_queries () in
                                             if uu____6409
                                             then
                                               let uu____6412 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6412
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6420 =
                                               let uu____6427 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6427) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6420 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6439 =
                                               let uu____6446 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6446,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6439 in
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
                                             let uu____6467 =
                                               let uu____6474 =
                                                 let uu____6475 =
                                                   let uu____6486 =
                                                     let uu____6487 =
                                                       let uu____6492 =
                                                         let uu____6493 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6493 in
                                                       (f_has_t, uu____6492) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6487 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6486) in
                                                 mkForall_fuel uu____6475 in
                                               (uu____6474,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6467 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6516 =
                                               let uu____6523 =
                                                 let uu____6524 =
                                                   let uu____6535 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6535) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6524 in
                                               (uu____6523,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6516 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6560 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6560);
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
                     let uu____6575 =
                       let uu____6582 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6582,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6575 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6594 =
                       let uu____6601 =
                         let uu____6602 =
                           let uu____6613 =
                             let uu____6614 =
                               let uu____6619 =
                                 let uu____6620 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6620 in
                               (f_has_t, uu____6619) in
                             FStar_SMTEncoding_Util.mkImp uu____6614 in
                           ([[f_has_t]], [fsym], uu____6613) in
                         mkForall_fuel uu____6602 in
                       (uu____6601, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6594 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6647 ->
           let uu____6654 =
             let uu____6659 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6659 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6666;
                 FStar_Syntax_Syntax.vars = uu____6667;_} ->
                 let uu____6674 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6674 with
                  | (b,f1) ->
                      let uu____6699 =
                        let uu____6700 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6700 in
                      (uu____6699, f1))
             | uu____6709 -> failwith "impossible" in
           (match uu____6654 with
            | (x,f) ->
                let uu____6720 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6720 with
                 | (base_t,decls) ->
                     let uu____6731 = gen_term_var env x in
                     (match uu____6731 with
                      | (x1,xtm,env') ->
                          let uu____6745 = encode_formula f env' in
                          (match uu____6745 with
                           | (refinement,decls') ->
                               let uu____6756 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6756 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6772 =
                                        let uu____6775 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6782 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6775
                                          uu____6782 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6772 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6815  ->
                                              match uu____6815 with
                                              | (y,uu____6821) ->
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
                                    let uu____6854 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6854 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6862 =
                                           let uu____6863 =
                                             let uu____6870 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6870) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6863 in
                                         (uu____6862,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6891 =
                                             let uu____6892 =
                                               let uu____6893 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6893 in
                                             Prims.strcat module_name
                                               uu____6892 in
                                           varops.mk_unique uu____6891 in
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
                                           let uu____6907 =
                                             let uu____6914 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6914) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6907 in
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
                                           let uu____6929 =
                                             let uu____6936 =
                                               let uu____6937 =
                                                 let uu____6948 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6948) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6937 in
                                             (uu____6936,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6929 in
                                         let t_kinding =
                                           let uu____6966 =
                                             let uu____6973 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6973,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6966 in
                                         let t_interp =
                                           let uu____6991 =
                                             let uu____6998 =
                                               let uu____6999 =
                                                 let uu____7010 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7010) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6999 in
                                             let uu____7033 =
                                               let uu____7036 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____7036 in
                                             (uu____6998, uu____7033,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6991 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7043 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7043);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7073 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7073 in
           let uu____7074 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7074 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7086 =
                    let uu____7093 =
                      let uu____7094 =
                        let uu____7095 =
                          let uu____7096 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7096 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7095 in
                      varops.mk_unique uu____7094 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7093) in
                  FStar_SMTEncoding_Util.mkAssume uu____7086 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7101 ->
           let uu____7116 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7116 with
            | (head1,args_e) ->
                let uu____7157 =
                  let uu____7170 =
                    let uu____7171 = FStar_Syntax_Subst.compress head1 in
                    uu____7171.FStar_Syntax_Syntax.n in
                  (uu____7170, args_e) in
                (match uu____7157 with
                 | uu____7186 when head_redex env head1 ->
                     let uu____7199 = whnf env t in
                     encode_term uu____7199 env
                 | uu____7200 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7219 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7233;
                       FStar_Syntax_Syntax.vars = uu____7234;_},uu____7235),uu____7236::
                    (v1,uu____7238)::(v2,uu____7240)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7291 = encode_term v1 env in
                     (match uu____7291 with
                      | (v11,decls1) ->
                          let uu____7302 = encode_term v2 env in
                          (match uu____7302 with
                           | (v21,decls2) ->
                               let uu____7313 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7313,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7317::(v1,uu____7319)::(v2,uu____7321)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7368 = encode_term v1 env in
                     (match uu____7368 with
                      | (v11,decls1) ->
                          let uu____7379 = encode_term v2 env in
                          (match uu____7379 with
                           | (v21,decls2) ->
                               let uu____7390 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7390,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7394)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7420)::(arg,uu____7422)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7457) ->
                     let e0 =
                       let uu____7475 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7475 in
                     ((let uu____7483 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7483
                       then
                         let uu____7484 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7484
                       else ());
                      (let e =
                         let uu____7489 =
                           let uu____7490 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7491 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7490
                             uu____7491 in
                         uu____7489 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7500),(arg,uu____7502)::[]) -> encode_term arg env
                 | uu____7527 ->
                     let uu____7540 = encode_args args_e env in
                     (match uu____7540 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7595 = encode_term head1 env in
                            match uu____7595 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7659 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7659 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7737  ->
                                                 fun uu____7738  ->
                                                   match (uu____7737,
                                                           uu____7738)
                                                   with
                                                   | ((bv,uu____7760),
                                                      (a,uu____7762)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7780 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7780
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7785 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7785 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7800 =
                                                   let uu____7807 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7816 =
                                                     let uu____7817 =
                                                       let uu____7818 =
                                                         let uu____7819 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7819 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7818 in
                                                     varops.mk_unique
                                                       uu____7817 in
                                                   (uu____7807,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7816) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7800 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7836 = lookup_free_var_sym env fv in
                            match uu____7836 with
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
                                   FStar_Syntax_Syntax.pos = uu____7867;
                                   FStar_Syntax_Syntax.vars = uu____7868;_},uu____7869)
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
                                   FStar_Syntax_Syntax.pos = uu____7880;
                                   FStar_Syntax_Syntax.vars = uu____7881;_},uu____7882)
                                ->
                                let uu____7887 =
                                  let uu____7888 =
                                    let uu____7893 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7893
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7888
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7887
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7923 =
                                  let uu____7924 =
                                    let uu____7929 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7929
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7924
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7923
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7958,(FStar_Util.Inl t1,uu____7960),uu____7961)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8010,(FStar_Util.Inr c,uu____8012),uu____8013)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8062 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8089 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8089 in
                               let uu____8090 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8090 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8106;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8107;_},uu____8108)
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
                                     | uu____8122 ->
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
           let uu____8171 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8171 with
            | (bs1,body1,opening) ->
                let fallback uu____8194 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8201 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8201, [decl]) in
                let is_impure rc =
                  let uu____8208 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8208 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8218 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8218
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8238 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8238
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8242 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8242)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8249 =
                         let uu____8250 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8250 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8249);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8252 =
                       (is_impure rc) &&
                         (let uu____8254 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8254) in
                     if uu____8252
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8261 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8261 with
                        | (vars,guards,envbody,decls,uu____8286) ->
                            let body2 =
                              let uu____8300 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc in
                              if uu____8300
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1 in
                            let uu____8302 = encode_term body2 envbody in
                            (match uu____8302 with
                             | (body3,decls') ->
                                 let uu____8313 =
                                   let uu____8322 = codomain_eff rc in
                                   match uu____8322 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____8341 = encode_term tfun env in
                                       (match uu____8341 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8313 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8373 =
                                          let uu____8384 =
                                            let uu____8385 =
                                              let uu____8390 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8390, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8385 in
                                          ([], vars, uu____8384) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8373 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8402 =
                                              let uu____8405 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8405
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8402 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8424 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8424 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8432 =
                                             let uu____8433 =
                                               let uu____8440 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8440) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8433 in
                                           (uu____8432,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8451 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8451 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8462 =
                                                    let uu____8463 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8463 = cache_size in
                                                  if uu____8462
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
                                                    let uu____8479 =
                                                      let uu____8480 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8480 in
                                                    varops.mk_unique
                                                      uu____8479 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8487 =
                                                    let uu____8494 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8494) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8487 in
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
                                                      let uu____8512 =
                                                        let uu____8513 =
                                                          let uu____8520 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8520,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8513 in
                                                      [uu____8512] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8533 =
                                                    let uu____8540 =
                                                      let uu____8541 =
                                                        let uu____8552 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8552) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8541 in
                                                    (uu____8540,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8533 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8569 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8569);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8572,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8573;
                          FStar_Syntax_Syntax.lbunivs = uu____8574;
                          FStar_Syntax_Syntax.lbtyp = uu____8575;
                          FStar_Syntax_Syntax.lbeff = uu____8576;
                          FStar_Syntax_Syntax.lbdef = uu____8577;_}::uu____8578),uu____8579)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8605;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8607;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8628 ->
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
              let uu____8698 = encode_term e1 env in
              match uu____8698 with
              | (ee1,decls1) ->
                  let uu____8709 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8709 with
                   | (xs,e21) ->
                       let uu____8734 = FStar_List.hd xs in
                       (match uu____8734 with
                        | (x1,uu____8748) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8750 = encode_body e21 env' in
                            (match uu____8750 with
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
            let uu____8782 =
              let uu____8789 =
                let uu____8790 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8790 in
              gen_term_var env uu____8789 in
            match uu____8782 with
            | (scrsym,scr',env1) ->
                let uu____8798 = encode_term e env1 in
                (match uu____8798 with
                 | (scr,decls) ->
                     let uu____8809 =
                       let encode_branch b uu____8834 =
                         match uu____8834 with
                         | (else_case,decls1) ->
                             let uu____8853 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____8853 with
                              | (p,w,br) ->
                                  let uu____8879 = encode_pat env1 p in
                                  (match uu____8879 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8916  ->
                                                   match uu____8916 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____8923 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8945 =
                                               encode_term w1 env2 in
                                             (match uu____8945 with
                                              | (w2,decls2) ->
                                                  let uu____8958 =
                                                    let uu____8959 =
                                                      let uu____8964 =
                                                        let uu____8965 =
                                                          let uu____8970 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____8970) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8965 in
                                                      (guard, uu____8964) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8959 in
                                                  (uu____8958, decls2)) in
                                       (match uu____8923 with
                                        | (guard1,decls2) ->
                                            let uu____8983 =
                                              encode_br br env2 in
                                            (match uu____8983 with
                                             | (br1,decls3) ->
                                                 let uu____8996 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____8996,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8809 with
                      | (match_tm,decls1) ->
                          let uu____9015 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9015, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9055 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9055
       then
         let uu____9056 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9056
       else ());
      (let uu____9058 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9058 with
       | (vars,pat_term) ->
           let uu____9075 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9128  ->
                     fun v1  ->
                       match uu____9128 with
                       | (env1,vars1) ->
                           let uu____9180 = gen_term_var env1 v1 in
                           (match uu____9180 with
                            | (xx,uu____9202,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9075 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9281 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9282 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9283 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9291 = encode_const c env1 in
                      (match uu____9291 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9305::uu____9306 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9309 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9332 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9332 with
                        | (uu____9339,uu____9340::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9343 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9376  ->
                                  match uu____9376 with
                                  | (arg,uu____9384) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9390 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9390)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9417) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9448 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9471 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9515  ->
                                  match uu____9515 with
                                  | (arg,uu____9529) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9535 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9535)) in
                      FStar_All.pipe_right uu____9471 FStar_List.flatten in
                let pat_term1 uu____9563 = encode_term pat_term env1 in
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
      let uu____9573 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9611  ->
                fun uu____9612  ->
                  match (uu____9611, uu____9612) with
                  | ((tms,decls),(t,uu____9648)) ->
                      let uu____9669 = encode_term t env in
                      (match uu____9669 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9573 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9726 = FStar_Syntax_Util.list_elements e in
        match uu____9726 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9747 =
          let uu____9762 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9762 FStar_Syntax_Util.head_and_args in
        match uu____9747 with
        | (head1,args) ->
            let uu____9801 =
              let uu____9814 =
                let uu____9815 = FStar_Syntax_Util.un_uinst head1 in
                uu____9815.FStar_Syntax_Syntax.n in
              (uu____9814, args) in
            (match uu____9801 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9829,uu____9830)::(e,uu____9832)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9867 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____9903 =
            let uu____9918 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____9918 FStar_Syntax_Util.head_and_args in
          match uu____9903 with
          | (head1,args) ->
              let uu____9959 =
                let uu____9972 =
                  let uu____9973 = FStar_Syntax_Util.un_uinst head1 in
                  uu____9973.FStar_Syntax_Syntax.n in
                (uu____9972, args) in
              (match uu____9959 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9990)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10017 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10039 = smt_pat_or1 t1 in
            (match uu____10039 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10055 = list_elements1 e in
                 FStar_All.pipe_right uu____10055
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10073 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10073
                           (FStar_List.map one_pat)))
             | uu____10084 ->
                 let uu____10089 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10089])
        | uu____10110 ->
            let uu____10113 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10113] in
      let uu____10134 =
        let uu____10153 =
          let uu____10154 = FStar_Syntax_Subst.compress t in
          uu____10154.FStar_Syntax_Syntax.n in
        match uu____10153 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10193 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10193 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10236;
                        FStar_Syntax_Syntax.effect_name = uu____10237;
                        FStar_Syntax_Syntax.result_typ = uu____10238;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10240)::(post,uu____10242)::(pats,uu____10244)::[];
                        FStar_Syntax_Syntax.flags = uu____10245;_}
                      ->
                      let uu____10286 = lemma_pats pats in
                      (binders1, pre, post, uu____10286)
                  | uu____10303 -> failwith "impos"))
        | uu____10322 -> failwith "Impos" in
      match uu____10134 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___395_10370 = env in
            {
              bindings = (uu___395_10370.bindings);
              depth = (uu___395_10370.depth);
              tcenv = (uu___395_10370.tcenv);
              warn = (uu___395_10370.warn);
              cache = (uu___395_10370.cache);
              nolabels = (uu___395_10370.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___395_10370.encode_non_total_function_typ);
              current_module_name = (uu___395_10370.current_module_name)
            } in
          let uu____10371 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10371 with
           | (vars,guards,env2,decls,uu____10396) ->
               let uu____10409 =
                 let uu____10422 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10466 =
                             let uu____10475 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10475
                               FStar_List.unzip in
                           match uu____10466 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10422 FStar_List.unzip in
               (match uu____10409 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post in
                    let env3 =
                      let uu___396_10587 = env2 in
                      {
                        bindings = (uu___396_10587.bindings);
                        depth = (uu___396_10587.depth);
                        tcenv = (uu___396_10587.tcenv);
                        warn = (uu___396_10587.warn);
                        cache = (uu___396_10587.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___396_10587.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___396_10587.encode_non_total_function_typ);
                        current_module_name =
                          (uu___396_10587.current_module_name)
                      } in
                    let uu____10588 =
                      let uu____10593 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10593 env3 in
                    (match uu____10588 with
                     | (pre1,decls'') ->
                         let uu____10600 =
                           let uu____10605 = FStar_Syntax_Util.unmeta post1 in
                           encode_formula uu____10605 env3 in
                         (match uu____10600 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____10615 =
                                let uu____10616 =
                                  let uu____10627 =
                                    let uu____10628 =
                                      let uu____10633 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____10633, post2) in
                                    FStar_SMTEncoding_Util.mkImp uu____10628 in
                                  (pats, vars, uu____10627) in
                                FStar_SMTEncoding_Util.mkForall uu____10616 in
                              (uu____10615, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10652 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____10652
        then
          let uu____10653 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____10654 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10653 uu____10654
        else () in
      let enc f r l =
        let uu____10687 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10715 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____10715 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____10687 with
        | (decls,args) ->
            let uu____10744 =
              let uu___397_10745 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___397_10745.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___397_10745.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10744, decls) in
      let const_op f r uu____10776 =
        let uu____10789 = f r in (uu____10789, []) in
      let un_op f l =
        let uu____10808 = FStar_List.hd l in
        FStar_All.pipe_left f uu____10808 in
      let bin_op f uu___371_10824 =
        match uu___371_10824 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10835 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____10869 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10892  ->
                 match uu____10892 with
                 | (t,uu____10906) ->
                     let uu____10907 = encode_formula t env in
                     (match uu____10907 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____10869 with
        | (decls,phis) ->
            let uu____10936 =
              let uu___398_10937 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___398_10937.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___398_10937.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____10936, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10998  ->
               match uu____10998 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11017) -> false
                    | uu____11018 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11033 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11033
        else
          (let uu____11047 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11047 r rf) in
      let mk_imp1 r uu___372_11072 =
        match uu___372_11072 with
        | (lhs,uu____11078)::(rhs,uu____11080)::[] ->
            let uu____11107 = encode_formula rhs env in
            (match uu____11107 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11122) ->
                      (l1, decls1)
                  | uu____11127 ->
                      let uu____11128 = encode_formula lhs env in
                      (match uu____11128 with
                       | (l2,decls2) ->
                           let uu____11139 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11139, (FStar_List.append decls1 decls2)))))
        | uu____11142 -> failwith "impossible" in
      let mk_ite r uu___373_11163 =
        match uu___373_11163 with
        | (guard,uu____11169)::(_then,uu____11171)::(_else,uu____11173)::[]
            ->
            let uu____11210 = encode_formula guard env in
            (match uu____11210 with
             | (g,decls1) ->
                 let uu____11221 = encode_formula _then env in
                 (match uu____11221 with
                  | (t,decls2) ->
                      let uu____11232 = encode_formula _else env in
                      (match uu____11232 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11246 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11271 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11271 in
      let connectives =
        let uu____11289 =
          let uu____11302 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11302) in
        let uu____11319 =
          let uu____11334 =
            let uu____11347 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11347) in
          let uu____11364 =
            let uu____11379 =
              let uu____11394 =
                let uu____11407 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11407) in
              let uu____11424 =
                let uu____11439 =
                  let uu____11454 =
                    let uu____11467 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11467) in
                  [uu____11454;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11439 in
              uu____11394 :: uu____11424 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11379 in
          uu____11334 :: uu____11364 in
        uu____11289 :: uu____11319 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11788 = encode_formula phi' env in
            (match uu____11788 with
             | (phi2,decls) ->
                 let uu____11799 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____11799, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11800 ->
            let uu____11807 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____11807 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11846 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____11846 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11858;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11860;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11881 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____11881 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11928::(x,uu____11930)::(t,uu____11932)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11979 = encode_term x env in
                 (match uu____11979 with
                  | (x1,decls) ->
                      let uu____11990 = encode_term t env in
                      (match uu____11990 with
                       | (t1,decls') ->
                           let uu____12001 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12001, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12006)::(msg,uu____12008)::(phi2,uu____12010)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12055 =
                   let uu____12060 =
                     let uu____12061 = FStar_Syntax_Subst.compress r in
                     uu____12061.FStar_Syntax_Syntax.n in
                   let uu____12064 =
                     let uu____12065 = FStar_Syntax_Subst.compress msg in
                     uu____12065.FStar_Syntax_Syntax.n in
                   (uu____12060, uu____12064) in
                 (match uu____12055 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12074))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12080 -> fallback phi2)
             | uu____12085 when head_redex env head2 ->
                 let uu____12098 = whnf env phi1 in
                 encode_formula uu____12098 env
             | uu____12099 ->
                 let uu____12112 = encode_term phi1 env in
                 (match uu____12112 with
                  | (tt,decls) ->
                      let uu____12123 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___399_12126 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___399_12126.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___399_12126.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12123, decls)))
        | uu____12127 ->
            let uu____12128 = encode_term phi1 env in
            (match uu____12128 with
             | (tt,decls) ->
                 let uu____12139 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___400_12142 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___400_12142.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___400_12142.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12139, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12178 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12178 with
        | (vars,guards,env2,decls,uu____12217) ->
            let uu____12230 =
              let uu____12243 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12291 =
                          let uu____12300 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12330  ->
                                    match uu____12330 with
                                    | (t,uu____12340) ->
                                        encode_term t
                                          (let uu___401_12342 = env2 in
                                           {
                                             bindings =
                                               (uu___401_12342.bindings);
                                             depth = (uu___401_12342.depth);
                                             tcenv = (uu___401_12342.tcenv);
                                             warn = (uu___401_12342.warn);
                                             cache = (uu___401_12342.cache);
                                             nolabels =
                                               (uu___401_12342.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___401_12342.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___401_12342.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12300 FStar_List.unzip in
                        match uu____12291 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12243 FStar_List.unzip in
            (match uu____12230 with
             | (pats,decls') ->
                 let uu____12441 = encode_formula body env2 in
                 (match uu____12441 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12473;
                             FStar_SMTEncoding_Term.rng = uu____12474;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12489 -> guards in
                      let uu____12494 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____12494, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12554  ->
                   match uu____12554 with
                   | (x,uu____12560) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12568 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12580 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____12580) uu____12568 tl1 in
             let uu____12583 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12610  ->
                       match uu____12610 with
                       | (b,uu____12616) ->
                           let uu____12617 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____12617)) in
             (match uu____12583 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12623) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____12637 =
                    let uu____12638 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12638 in
                  FStar_Errors.warn pos uu____12637) in
       let uu____12639 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____12639 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12648 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12706  ->
                     match uu____12706 with
                     | (l,uu____12720) -> FStar_Ident.lid_equals op l)) in
           (match uu____12648 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12753,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12793 = encode_q_body env vars pats body in
             match uu____12793 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12838 =
                     let uu____12849 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____12849) in
                   FStar_SMTEncoding_Term.mkForall uu____12838
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12868 = encode_q_body env vars pats body in
             match uu____12868 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12912 =
                   let uu____12913 =
                     let uu____12924 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____12924) in
                   FStar_SMTEncoding_Term.mkExists uu____12913
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____12912, decls))))
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
  let uu____13017 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13017 with
  | (asym,a) ->
      let uu____13024 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13024 with
       | (xsym,x) ->
           let uu____13031 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13031 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13075 =
                      let uu____13086 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13086, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13075 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13112 =
                      let uu____13119 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13119) in
                    FStar_SMTEncoding_Util.mkApp uu____13112 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13132 =
                    let uu____13135 =
                      let uu____13138 =
                        let uu____13141 =
                          let uu____13142 =
                            let uu____13149 =
                              let uu____13150 =
                                let uu____13161 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13161) in
                              FStar_SMTEncoding_Util.mkForall uu____13150 in
                            (uu____13149, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13142 in
                        let uu____13178 =
                          let uu____13181 =
                            let uu____13182 =
                              let uu____13189 =
                                let uu____13190 =
                                  let uu____13201 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13201) in
                                FStar_SMTEncoding_Util.mkForall uu____13190 in
                              (uu____13189,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13182 in
                          [uu____13181] in
                        uu____13141 :: uu____13178 in
                      xtok_decl :: uu____13138 in
                    xname_decl :: uu____13135 in
                  (xtok1, uu____13132) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13292 =
                    let uu____13305 =
                      let uu____13314 =
                        let uu____13315 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13315 in
                      quant axy uu____13314 in
                    (FStar_Parser_Const.op_Eq, uu____13305) in
                  let uu____13324 =
                    let uu____13339 =
                      let uu____13352 =
                        let uu____13361 =
                          let uu____13362 =
                            let uu____13363 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13363 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13362 in
                        quant axy uu____13361 in
                      (FStar_Parser_Const.op_notEq, uu____13352) in
                    let uu____13372 =
                      let uu____13387 =
                        let uu____13400 =
                          let uu____13409 =
                            let uu____13410 =
                              let uu____13411 =
                                let uu____13416 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13417 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13416, uu____13417) in
                              FStar_SMTEncoding_Util.mkLT uu____13411 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13410 in
                          quant xy uu____13409 in
                        (FStar_Parser_Const.op_LT, uu____13400) in
                      let uu____13426 =
                        let uu____13441 =
                          let uu____13454 =
                            let uu____13463 =
                              let uu____13464 =
                                let uu____13465 =
                                  let uu____13470 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____13471 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____13470, uu____13471) in
                                FStar_SMTEncoding_Util.mkLTE uu____13465 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13464 in
                            quant xy uu____13463 in
                          (FStar_Parser_Const.op_LTE, uu____13454) in
                        let uu____13480 =
                          let uu____13495 =
                            let uu____13508 =
                              let uu____13517 =
                                let uu____13518 =
                                  let uu____13519 =
                                    let uu____13524 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____13525 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____13524, uu____13525) in
                                  FStar_SMTEncoding_Util.mkGT uu____13519 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13518 in
                              quant xy uu____13517 in
                            (FStar_Parser_Const.op_GT, uu____13508) in
                          let uu____13534 =
                            let uu____13549 =
                              let uu____13562 =
                                let uu____13571 =
                                  let uu____13572 =
                                    let uu____13573 =
                                      let uu____13578 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____13579 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____13578, uu____13579) in
                                    FStar_SMTEncoding_Util.mkGTE uu____13573 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13572 in
                                quant xy uu____13571 in
                              (FStar_Parser_Const.op_GTE, uu____13562) in
                            let uu____13588 =
                              let uu____13603 =
                                let uu____13616 =
                                  let uu____13625 =
                                    let uu____13626 =
                                      let uu____13627 =
                                        let uu____13632 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____13633 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____13632, uu____13633) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13627 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13626 in
                                  quant xy uu____13625 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13616) in
                              let uu____13642 =
                                let uu____13657 =
                                  let uu____13670 =
                                    let uu____13679 =
                                      let uu____13680 =
                                        let uu____13681 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13681 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13680 in
                                    quant qx uu____13679 in
                                  (FStar_Parser_Const.op_Minus, uu____13670) in
                                let uu____13690 =
                                  let uu____13705 =
                                    let uu____13718 =
                                      let uu____13727 =
                                        let uu____13728 =
                                          let uu____13729 =
                                            let uu____13734 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____13735 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____13734, uu____13735) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13729 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13728 in
                                      quant xy uu____13727 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13718) in
                                  let uu____13744 =
                                    let uu____13759 =
                                      let uu____13772 =
                                        let uu____13781 =
                                          let uu____13782 =
                                            let uu____13783 =
                                              let uu____13788 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____13789 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____13788, uu____13789) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13783 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13782 in
                                        quant xy uu____13781 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13772) in
                                    let uu____13798 =
                                      let uu____13813 =
                                        let uu____13826 =
                                          let uu____13835 =
                                            let uu____13836 =
                                              let uu____13837 =
                                                let uu____13842 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____13843 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____13842, uu____13843) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13837 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13836 in
                                          quant xy uu____13835 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13826) in
                                      let uu____13852 =
                                        let uu____13867 =
                                          let uu____13880 =
                                            let uu____13889 =
                                              let uu____13890 =
                                                let uu____13891 =
                                                  let uu____13896 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____13897 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____13896, uu____13897) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13891 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13890 in
                                            quant xy uu____13889 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13880) in
                                        let uu____13906 =
                                          let uu____13921 =
                                            let uu____13934 =
                                              let uu____13943 =
                                                let uu____13944 =
                                                  let uu____13945 =
                                                    let uu____13950 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____13951 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____13950,
                                                      uu____13951) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____13945 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____13944 in
                                              quant xy uu____13943 in
                                            (FStar_Parser_Const.op_And,
                                              uu____13934) in
                                          let uu____13960 =
                                            let uu____13975 =
                                              let uu____13988 =
                                                let uu____13997 =
                                                  let uu____13998 =
                                                    let uu____13999 =
                                                      let uu____14004 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14005 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14004,
                                                        uu____14005) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____13999 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____13998 in
                                                quant xy uu____13997 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____13988) in
                                            let uu____14014 =
                                              let uu____14029 =
                                                let uu____14042 =
                                                  let uu____14051 =
                                                    let uu____14052 =
                                                      let uu____14053 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14053 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14052 in
                                                  quant qx uu____14051 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14042) in
                                              [uu____14029] in
                                            uu____13975 :: uu____14014 in
                                          uu____13921 :: uu____13960 in
                                        uu____13867 :: uu____13906 in
                                      uu____13813 :: uu____13852 in
                                    uu____13759 :: uu____13798 in
                                  uu____13705 :: uu____13744 in
                                uu____13657 :: uu____13690 in
                              uu____13603 :: uu____13642 in
                            uu____13549 :: uu____13588 in
                          uu____13495 :: uu____13534 in
                        uu____13441 :: uu____13480 in
                      uu____13387 :: uu____13426 in
                    uu____13339 :: uu____13372 in
                  uu____13292 :: uu____13324 in
                let mk1 l v1 =
                  let uu____14267 =
                    let uu____14276 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14334  ->
                              match uu____14334 with
                              | (l',uu____14348) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14276
                      (FStar_Option.map
                         (fun uu____14408  ->
                            match uu____14408 with | (uu____14427,b) -> b v1)) in
                  FStar_All.pipe_right uu____14267 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14498  ->
                          match uu____14498 with
                          | (l',uu____14512) -> FStar_Ident.lid_equals l l')) in
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
        let uu____14550 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____14550 with
        | (xxsym,xx) ->
            let uu____14557 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____14557 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____14567 =
                   let uu____14574 =
                     let uu____14575 =
                       let uu____14586 =
                         let uu____14587 =
                           let uu____14592 =
                             let uu____14593 =
                               let uu____14598 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____14598) in
                             FStar_SMTEncoding_Util.mkEq uu____14593 in
                           (xx_has_type, uu____14592) in
                         FStar_SMTEncoding_Util.mkImp uu____14587 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14586) in
                     FStar_SMTEncoding_Util.mkForall uu____14575 in
                   let uu____14623 =
                     let uu____14624 =
                       let uu____14625 =
                         let uu____14626 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____14626 in
                       Prims.strcat module_name uu____14625 in
                     varops.mk_unique uu____14624 in
                   (uu____14574, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14623) in
                 FStar_SMTEncoding_Util.mkAssume uu____14567)
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
    let uu____14662 =
      let uu____14663 =
        let uu____14670 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____14670, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14663 in
    let uu____14673 =
      let uu____14676 =
        let uu____14677 =
          let uu____14684 =
            let uu____14685 =
              let uu____14696 =
                let uu____14697 =
                  let uu____14702 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____14702) in
                FStar_SMTEncoding_Util.mkImp uu____14697 in
              ([[typing_pred]], [xx], uu____14696) in
            mkForall_fuel uu____14685 in
          (uu____14684, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14677 in
      [uu____14676] in
    uu____14662 :: uu____14673 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____14744 =
      let uu____14745 =
        let uu____14752 =
          let uu____14753 =
            let uu____14764 =
              let uu____14769 =
                let uu____14772 = FStar_SMTEncoding_Term.boxBool b in
                [uu____14772] in
              [uu____14769] in
            let uu____14777 =
              let uu____14778 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____14778 tt in
            (uu____14764, [bb], uu____14777) in
          FStar_SMTEncoding_Util.mkForall uu____14753 in
        (uu____14752, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14745 in
    let uu____14799 =
      let uu____14802 =
        let uu____14803 =
          let uu____14810 =
            let uu____14811 =
              let uu____14822 =
                let uu____14823 =
                  let uu____14828 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____14828) in
                FStar_SMTEncoding_Util.mkImp uu____14823 in
              ([[typing_pred]], [xx], uu____14822) in
            mkForall_fuel uu____14811 in
          (uu____14810, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14803 in
      [uu____14802] in
    uu____14744 :: uu____14799 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____14878 =
        let uu____14879 =
          let uu____14886 =
            let uu____14889 =
              let uu____14892 =
                let uu____14895 = FStar_SMTEncoding_Term.boxInt a in
                let uu____14896 =
                  let uu____14899 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____14899] in
                uu____14895 :: uu____14896 in
              tt :: uu____14892 in
            tt :: uu____14889 in
          ("Prims.Precedes", uu____14886) in
        FStar_SMTEncoding_Util.mkApp uu____14879 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14878 in
    let precedes_y_x =
      let uu____14903 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14903 in
    let uu____14906 =
      let uu____14907 =
        let uu____14914 =
          let uu____14915 =
            let uu____14926 =
              let uu____14931 =
                let uu____14934 = FStar_SMTEncoding_Term.boxInt b in
                [uu____14934] in
              [uu____14931] in
            let uu____14939 =
              let uu____14940 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____14940 tt in
            (uu____14926, [bb], uu____14939) in
          FStar_SMTEncoding_Util.mkForall uu____14915 in
        (uu____14914, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____14907 in
    let uu____14961 =
      let uu____14964 =
        let uu____14965 =
          let uu____14972 =
            let uu____14973 =
              let uu____14984 =
                let uu____14985 =
                  let uu____14990 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____14990) in
                FStar_SMTEncoding_Util.mkImp uu____14985 in
              ([[typing_pred]], [xx], uu____14984) in
            mkForall_fuel uu____14973 in
          (uu____14972, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____14965 in
      let uu____15015 =
        let uu____15018 =
          let uu____15019 =
            let uu____15026 =
              let uu____15027 =
                let uu____15038 =
                  let uu____15039 =
                    let uu____15044 =
                      let uu____15045 =
                        let uu____15048 =
                          let uu____15051 =
                            let uu____15054 =
                              let uu____15055 =
                                let uu____15060 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15061 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15060, uu____15061) in
                              FStar_SMTEncoding_Util.mkGT uu____15055 in
                            let uu____15062 =
                              let uu____15065 =
                                let uu____15066 =
                                  let uu____15071 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15072 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15071, uu____15072) in
                                FStar_SMTEncoding_Util.mkGTE uu____15066 in
                              let uu____15073 =
                                let uu____15076 =
                                  let uu____15077 =
                                    let uu____15082 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15083 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15082, uu____15083) in
                                  FStar_SMTEncoding_Util.mkLT uu____15077 in
                                [uu____15076] in
                              uu____15065 :: uu____15073 in
                            uu____15054 :: uu____15062 in
                          typing_pred_y :: uu____15051 in
                        typing_pred :: uu____15048 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15045 in
                    (uu____15044, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15039 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15038) in
              mkForall_fuel uu____15027 in
            (uu____15026,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15019 in
        [uu____15018] in
      uu____14964 :: uu____15015 in
    uu____14906 :: uu____14961 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15129 =
      let uu____15130 =
        let uu____15137 =
          let uu____15138 =
            let uu____15149 =
              let uu____15154 =
                let uu____15157 = FStar_SMTEncoding_Term.boxString b in
                [uu____15157] in
              [uu____15154] in
            let uu____15162 =
              let uu____15163 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15163 tt in
            (uu____15149, [bb], uu____15162) in
          FStar_SMTEncoding_Util.mkForall uu____15138 in
        (uu____15137, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15130 in
    let uu____15184 =
      let uu____15187 =
        let uu____15188 =
          let uu____15195 =
            let uu____15196 =
              let uu____15207 =
                let uu____15208 =
                  let uu____15213 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15213) in
                FStar_SMTEncoding_Util.mkImp uu____15208 in
              ([[typing_pred]], [xx], uu____15207) in
            mkForall_fuel uu____15196 in
          (uu____15195, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15188 in
      [uu____15187] in
    uu____15129 :: uu____15184 in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15266 =
      let uu____15267 =
        let uu____15274 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15274, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15267 in
    [uu____15266] in
  let mk_and_interp env conj uu____15286 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15311 =
      let uu____15312 =
        let uu____15319 =
          let uu____15320 =
            let uu____15331 =
              let uu____15332 =
                let uu____15337 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____15337, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15332 in
            ([[l_and_a_b]], [aa; bb], uu____15331) in
          FStar_SMTEncoding_Util.mkForall uu____15320 in
        (uu____15319, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15312 in
    [uu____15311] in
  let mk_or_interp env disj uu____15375 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15400 =
      let uu____15401 =
        let uu____15408 =
          let uu____15409 =
            let uu____15420 =
              let uu____15421 =
                let uu____15426 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____15426, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15421 in
            ([[l_or_a_b]], [aa; bb], uu____15420) in
          FStar_SMTEncoding_Util.mkForall uu____15409 in
        (uu____15408, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15401 in
    [uu____15400] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____15489 =
      let uu____15490 =
        let uu____15497 =
          let uu____15498 =
            let uu____15509 =
              let uu____15510 =
                let uu____15515 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15515, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15510 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15509) in
          FStar_SMTEncoding_Util.mkForall uu____15498 in
        (uu____15497, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15490 in
    [uu____15489] in
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
    let uu____15588 =
      let uu____15589 =
        let uu____15596 =
          let uu____15597 =
            let uu____15608 =
              let uu____15609 =
                let uu____15614 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____15614, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15609 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15608) in
          FStar_SMTEncoding_Util.mkForall uu____15597 in
        (uu____15596, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15589 in
    [uu____15588] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15685 =
      let uu____15686 =
        let uu____15693 =
          let uu____15694 =
            let uu____15705 =
              let uu____15706 =
                let uu____15711 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____15711, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15706 in
            ([[l_imp_a_b]], [aa; bb], uu____15705) in
          FStar_SMTEncoding_Util.mkForall uu____15694 in
        (uu____15693, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15686 in
    [uu____15685] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15774 =
      let uu____15775 =
        let uu____15782 =
          let uu____15783 =
            let uu____15794 =
              let uu____15795 =
                let uu____15800 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____15800, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15795 in
            ([[l_iff_a_b]], [aa; bb], uu____15794) in
          FStar_SMTEncoding_Util.mkForall uu____15783 in
        (uu____15782, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15775 in
    [uu____15774] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____15852 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15852 in
    let uu____15855 =
      let uu____15856 =
        let uu____15863 =
          let uu____15864 =
            let uu____15875 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____15875) in
          FStar_SMTEncoding_Util.mkForall uu____15864 in
        (uu____15863, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15856 in
    [uu____15855] in
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
      let uu____15935 =
        let uu____15942 =
          let uu____15945 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____15945] in
        ("Valid", uu____15942) in
      FStar_SMTEncoding_Util.mkApp uu____15935 in
    let uu____15948 =
      let uu____15949 =
        let uu____15956 =
          let uu____15957 =
            let uu____15968 =
              let uu____15969 =
                let uu____15974 =
                  let uu____15975 =
                    let uu____15986 =
                      let uu____15991 =
                        let uu____15994 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____15994] in
                      [uu____15991] in
                    let uu____15999 =
                      let uu____16000 =
                        let uu____16005 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16005, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16000 in
                    (uu____15986, [xx1], uu____15999) in
                  FStar_SMTEncoding_Util.mkForall uu____15975 in
                (uu____15974, valid) in
              FStar_SMTEncoding_Util.mkIff uu____15969 in
            ([[l_forall_a_b]], [aa; bb], uu____15968) in
          FStar_SMTEncoding_Util.mkForall uu____15957 in
        (uu____15956, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15949 in
    [uu____15948] in
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
      let uu____16087 =
        let uu____16094 =
          let uu____16097 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16097] in
        ("Valid", uu____16094) in
      FStar_SMTEncoding_Util.mkApp uu____16087 in
    let uu____16100 =
      let uu____16101 =
        let uu____16108 =
          let uu____16109 =
            let uu____16120 =
              let uu____16121 =
                let uu____16126 =
                  let uu____16127 =
                    let uu____16138 =
                      let uu____16143 =
                        let uu____16146 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16146] in
                      [uu____16143] in
                    let uu____16151 =
                      let uu____16152 =
                        let uu____16157 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16157, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16152 in
                    (uu____16138, [xx1], uu____16151) in
                  FStar_SMTEncoding_Util.mkExists uu____16127 in
                (uu____16126, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16121 in
            ([[l_exists_a_b]], [aa; bb], uu____16120) in
          FStar_SMTEncoding_Util.mkForall uu____16109 in
        (uu____16108, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16101 in
    [uu____16100] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16217 =
      let uu____16218 =
        let uu____16225 =
          let uu____16226 = FStar_SMTEncoding_Term.mk_Range_const () in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16226 range_ty in
        let uu____16227 = varops.mk_unique "typing_range_const" in
        (uu____16225, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16227) in
      FStar_SMTEncoding_Util.mkAssume uu____16218 in
    [uu____16217] in
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
        let uu____16261 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16261 x1 t in
      let uu____16262 =
        let uu____16273 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS) in
        ([[hastypeZ]], [xx1], uu____16273) in
      FStar_SMTEncoding_Util.mkForall uu____16262 in
    let uu____16296 =
      let uu____16297 =
        let uu____16304 =
          let uu____16305 =
            let uu____16316 = FStar_SMTEncoding_Util.mkImp (valid, body) in
            ([[inversion_t]], [tt1], uu____16316) in
          FStar_SMTEncoding_Util.mkForall uu____16305 in
        (uu____16304,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16297 in
    [uu____16296] in
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
          let uu____16640 =
            FStar_Util.find_opt
              (fun uu____16666  ->
                 match uu____16666 with
                 | (l,uu____16678) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____16640 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16703,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____16739 = encode_function_type_as_formula t env in
        match uu____16739 with
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
              let uu____16779 =
                ((let uu____16782 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm) in
                  FStar_All.pipe_left Prims.op_Negation uu____16782) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted in
              if uu____16779
              then
                let uu____16789 = new_term_constant_and_tok_from_lid env lid in
                match uu____16789 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16808 =
                        let uu____16809 = FStar_Syntax_Subst.compress t_norm in
                        uu____16809.FStar_Syntax_Syntax.n in
                      match uu____16808 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16815) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____16845  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____16850 -> [] in
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
                (let uu____16864 = prims.is lid in
                 if uu____16864
                 then
                   let vname = varops.new_fvar lid in
                   let uu____16872 = prims.mk lid vname in
                   match uu____16872 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok) in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims" in
                    let uu____16896 =
                      let uu____16907 = curried_arrow_formals_comp t_norm in
                      match uu____16907 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____16925 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp in
                            if uu____16925
                            then
                              let uu____16926 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___402_16929 = env.tcenv in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___402_16929.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___402_16929.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___402_16929.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___402_16929.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___402_16929.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___402_16929.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___402_16929.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___402_16929.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___402_16929.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___402_16929.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___402_16929.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___402_16929.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___402_16929.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___402_16929.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___402_16929.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___402_16929.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___402_16929.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___402_16929.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___402_16929.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___402_16929.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___402_16929.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___402_16929.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___402_16929.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___402_16929.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___402_16929.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___402_16929.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___402_16929.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___402_16929.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___402_16929.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___402_16929.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___402_16929.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___402_16929.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___402_16929.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown in
                              FStar_Syntax_Syntax.mk_Total uu____16926
                            else comp in
                          if encode_non_total_function_typ
                          then
                            let uu____16941 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1 in
                            (args, uu____16941)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1))) in
                    match uu____16896 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____16986 =
                          new_term_constant_and_tok_from_lid env lid in
                        (match uu____16986 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17007 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, []) in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___374_17049  ->
                                       match uu___374_17049 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17053 =
                                             FStar_Util.prefix vars in
                                           (match uu____17053 with
                                            | (uu____17074,(xxsym,uu____17076))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort) in
                                                let uu____17094 =
                                                  let uu____17095 =
                                                    let uu____17102 =
                                                      let uu____17103 =
                                                        let uu____17114 =
                                                          let uu____17115 =
                                                            let uu____17120 =
                                                              let uu____17121
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17121 in
                                                            (vapp,
                                                              uu____17120) in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17115 in
                                                        ([[vapp]], vars,
                                                          uu____17114) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17103 in
                                                    (uu____17102,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str))) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17095 in
                                                [uu____17094])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17140 =
                                             FStar_Util.prefix vars in
                                           (match uu____17140 with
                                            | (uu____17161,(xxsym,uu____17163))
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
                                                let uu____17186 =
                                                  let uu____17187 =
                                                    let uu____17194 =
                                                      let uu____17195 =
                                                        let uu____17206 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app) in
                                                        ([[vapp]], vars,
                                                          uu____17206) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17195 in
                                                    (uu____17194,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name)) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17187 in
                                                [uu____17186])
                                       | uu____17223 -> [])) in
                             let uu____17224 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1 in
                             (match uu____17224 with
                              | (vars,guards,env',decls1,uu____17251) ->
                                  let uu____17264 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17273 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards in
                                        (uu____17273, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17275 =
                                          encode_formula p env' in
                                        (match uu____17275 with
                                         | (g,ds) ->
                                             let uu____17286 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards) in
                                             (uu____17286,
                                               (FStar_List.append decls1 ds))) in
                                  (match uu____17264 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars in
                                       let vapp =
                                         let uu____17299 =
                                           let uu____17306 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars in
                                           (vname, uu____17306) in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17299 in
                                       let uu____17315 =
                                         let vname_decl =
                                           let uu____17323 =
                                             let uu____17334 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17344  ->
                                                       FStar_SMTEncoding_Term.Term_sort)) in
                                             (vname, uu____17334,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17323 in
                                         let uu____17353 =
                                           let env2 =
                                             let uu___403_17359 = env1 in
                                             {
                                               bindings =
                                                 (uu___403_17359.bindings);
                                               depth = (uu___403_17359.depth);
                                               tcenv = (uu___403_17359.tcenv);
                                               warn = (uu___403_17359.warn);
                                               cache = (uu___403_17359.cache);
                                               nolabels =
                                                 (uu___403_17359.nolabels);
                                               use_zfuel_name =
                                                 (uu___403_17359.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___403_17359.current_module_name)
                                             } in
                                           let uu____17360 =
                                             let uu____17361 =
                                               head_normal env2 tt in
                                             Prims.op_Negation uu____17361 in
                                           if uu____17360
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm in
                                         match uu____17353 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17376::uu____17377 ->
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
                                                     let uu____17417 =
                                                       let uu____17428 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17428) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17417 in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17455 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname)) in
                                             let uu____17458 =
                                               match formals with
                                               | [] ->
                                                   let uu____17475 =
                                                     let uu____17476 =
                                                       let uu____17479 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort) in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17479 in
                                                     push_free_var env1 lid
                                                       vname uu____17476 in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17475)
                                               | uu____17484 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None) in
                                                   let name_tok_corr =
                                                     let uu____17491 =
                                                       let uu____17498 =
                                                         let uu____17499 =
                                                           let uu____17510 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp) in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17510) in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17499 in
                                                       (uu____17498,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname)) in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17491 in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1) in
                                             (match uu____17458 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2)) in
                                       (match uu____17315 with
                                        | (decls2,env2) ->
                                            let uu____17553 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t in
                                              let uu____17561 =
                                                encode_term res_t1 env' in
                                              match uu____17561 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17574 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t in
                                                  (encoded_res_t,
                                                    uu____17574, decls) in
                                            (match uu____17553 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17585 =
                                                     let uu____17592 =
                                                       let uu____17593 =
                                                         let uu____17604 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred) in
                                                         ([[vapp]], vars,
                                                           uu____17604) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17593 in
                                                     (uu____17592,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17585 in
                                                 let freshness =
                                                   let uu____17620 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New) in
                                                   if uu____17620
                                                   then
                                                     let uu____17625 =
                                                       let uu____17626 =
                                                         let uu____17637 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         let uu____17648 =
                                                           varops.next_id () in
                                                         (vname, uu____17637,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17648) in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17626 in
                                                     let uu____17651 =
                                                       let uu____17654 =
                                                         pretype_axiom env2
                                                           vapp vars in
                                                       [uu____17654] in
                                                     uu____17625 ::
                                                       uu____17651
                                                   else [] in
                                                 let g =
                                                   let uu____17659 =
                                                     let uu____17662 =
                                                       let uu____17665 =
                                                         let uu____17668 =
                                                           let uu____17671 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars in
                                                           typingAx ::
                                                             uu____17671 in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17668 in
                                                       FStar_List.append
                                                         decls3 uu____17665 in
                                                     FStar_List.append decls2
                                                       uu____17662 in
                                                   FStar_List.append decls11
                                                     uu____17659 in
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
          let uu____17702 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____17702 with
          | FStar_Pervasives_Native.None  ->
              let uu____17739 = encode_free_var false env x t t_norm [] in
              (match uu____17739 with
               | (decls,env1) ->
                   let uu____17766 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____17766 with
                    | (n1,x',uu____17793) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17814) ->
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
            let uu____17869 =
              encode_free_var uninterpreted env lid t tt quals in
            match uu____17869 with
            | (decls,env1) ->
                let uu____17888 = FStar_Syntax_Util.is_smt_lemma t in
                if uu____17888
                then
                  let uu____17895 =
                    let uu____17898 = encode_smt_lemma env1 lid tt in
                    FStar_List.append decls uu____17898 in
                  (uu____17895, env1)
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
             (fun uu____17950  ->
                fun lb  ->
                  match uu____17950 with
                  | (decls,env1) ->
                      let uu____17970 =
                        let uu____17977 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val false env1 uu____17977
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____17970 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____17998 = FStar_Syntax_Util.head_and_args t in
    match uu____17998 with
    | (hd1,args) ->
        let uu____18035 =
          let uu____18036 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18036.FStar_Syntax_Syntax.n in
        (match uu____18035 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18040,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18059 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18081  ->
      fun quals  ->
        match uu____18081 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18157 = FStar_Util.first_N nbinders formals in
              match uu____18157 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18238  ->
                         fun uu____18239  ->
                           match (uu____18238, uu____18239) with
                           | ((formal,uu____18257),(binder,uu____18259)) ->
                               let uu____18268 =
                                 let uu____18275 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18275) in
                               FStar_Syntax_Syntax.NT uu____18268) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18283 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18314  ->
                              match uu____18314 with
                              | (x,i) ->
                                  let uu____18325 =
                                    let uu___404_18326 = x in
                                    let uu____18327 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___404_18326.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___404_18326.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18327
                                    } in
                                  (uu____18325, i))) in
                    FStar_All.pipe_right uu____18283
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18345 =
                      let uu____18346 = FStar_Syntax_Subst.compress body in
                      let uu____18347 =
                        let uu____18348 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18348 in
                      FStar_Syntax_Syntax.extend_app_n uu____18346
                        uu____18347 in
                    uu____18345 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18409 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____18409
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___405_18412 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___405_18412.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___405_18412.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___405_18412.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___405_18412.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___405_18412.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___405_18412.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___405_18412.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___405_18412.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___405_18412.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___405_18412.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___405_18412.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___405_18412.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___405_18412.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___405_18412.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___405_18412.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___405_18412.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___405_18412.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___405_18412.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___405_18412.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___405_18412.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___405_18412.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___405_18412.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___405_18412.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___405_18412.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___405_18412.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___405_18412.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___405_18412.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___405_18412.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___405_18412.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___405_18412.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___405_18412.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___405_18412.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___405_18412.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____18445 = FStar_Syntax_Util.abs_formals e in
                match uu____18445 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18509::uu____18510 ->
                         let uu____18525 =
                           let uu____18526 =
                             let uu____18529 =
                               FStar_Syntax_Subst.compress t_norm1 in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18529 in
                           uu____18526.FStar_Syntax_Syntax.n in
                         (match uu____18525 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18572 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____18572 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____18614 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____18614
                                   then
                                     let uu____18649 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____18649 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18743  ->
                                                   fun uu____18744  ->
                                                     match (uu____18743,
                                                             uu____18744)
                                                     with
                                                     | ((x,uu____18762),
                                                        (b,uu____18764)) ->
                                                         let uu____18773 =
                                                           let uu____18780 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____18780) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18773)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____18782 =
                                            let uu____18803 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____18803) in
                                          (uu____18782, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____18871 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____18871 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____18960) ->
                              let uu____18965 =
                                let uu____18986 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____18986 in
                              (uu____18965, true)
                          | uu____19051 when Prims.op_Negation norm1 ->
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
                          | uu____19053 ->
                              let uu____19054 =
                                let uu____19055 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19056 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19055
                                  uu____19056 in
                              failwith uu____19054)
                     | uu____19081 ->
                         let rec aux' t_norm2 =
                           let uu____19106 =
                             let uu____19107 =
                               FStar_Syntax_Subst.compress t_norm2 in
                             uu____19107.FStar_Syntax_Syntax.n in
                           match uu____19106 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19148 =
                                 FStar_Syntax_Subst.open_comp formals c in
                               (match uu____19148 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1 in
                                    let uu____19176 =
                                      eta_expand1 [] formals1 e tres in
                                    (match uu____19176 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19256)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19261 -> (([], e, [], t_norm2), false) in
                         aux' t_norm1) in
              aux false t_norm in
            (try
               let uu____19317 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19317
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19329 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19423  ->
                            fun lb  ->
                              match uu____19423 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19518 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____19518
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____19521 =
                                      let uu____19536 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____19536
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____19521 with
                                    | (tok,decl,env2) ->
                                        let uu____19582 =
                                          let uu____19595 =
                                            let uu____19606 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____19606, tok) in
                                          uu____19595 :: toks in
                                        (uu____19582, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19329 with
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
                        | uu____19789 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19797 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____19797 vars)
                            else
                              (let uu____19799 =
                                 let uu____19806 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____19806) in
                               FStar_SMTEncoding_Util.mkApp uu____19799) in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____19888;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____19890;
                             FStar_Syntax_Syntax.lbeff = uu____19891;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                            let uu____19954 =
                              let uu____19961 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm] in
                              match uu____19961 with
                              | (tcenv',uu____19979,e_t) ->
                                  let uu____19985 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____19996 -> failwith "Impossible" in
                                  (match uu____19985 with
                                   | (e1,t_norm1) ->
                                       ((let uu___408_20012 = env2 in
                                         {
                                           bindings =
                                             (uu___408_20012.bindings);
                                           depth = (uu___408_20012.depth);
                                           tcenv = tcenv';
                                           warn = (uu___408_20012.warn);
                                           cache = (uu___408_20012.cache);
                                           nolabels =
                                             (uu___408_20012.nolabels);
                                           use_zfuel_name =
                                             (uu___408_20012.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___408_20012.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___408_20012.current_module_name)
                                         }), e1, t_norm1)) in
                            (match uu____19954 with
                             | (env',e1,t_norm1) ->
                                 let uu____20022 =
                                   destruct_bound_function flid t_norm1 e1 in
                                 (match uu____20022 with
                                  | ((binders,body,uu____20043,uu____20044),curry)
                                      ->
                                      ((let uu____20055 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding") in
                                        if uu____20055
                                        then
                                          let uu____20056 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders in
                                          let uu____20057 =
                                            FStar_Syntax_Print.term_to_string
                                              body in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20056 uu____20057
                                        else ());
                                       (let uu____20059 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env' in
                                        match uu____20059 with
                                        | (vars,guards,env'1,binder_decls,uu____20086)
                                            ->
                                            let body1 =
                                              let uu____20100 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1 in
                                              if uu____20100
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body in
                                            let app =
                                              mk_app1 curry f ftok vars in
                                            let uu____20103 =
                                              let uu____20112 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic) in
                                              if uu____20112
                                              then
                                                let uu____20123 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app in
                                                let uu____20124 =
                                                  encode_formula body1 env'1 in
                                                (uu____20123, uu____20124)
                                              else
                                                (let uu____20134 =
                                                   encode_term body1 env'1 in
                                                 (app, uu____20134)) in
                                            (match uu____20103 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20157 =
                                                     let uu____20164 =
                                                       let uu____20165 =
                                                         let uu____20176 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2) in
                                                         ([[app1]], vars,
                                                           uu____20176) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20165 in
                                                     let uu____20187 =
                                                       let uu____20190 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20190 in
                                                     (uu____20164,
                                                       uu____20187,
                                                       (Prims.strcat
                                                          "equation_" f)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20157 in
                                                 let uu____20193 =
                                                   let uu____20196 =
                                                     let uu____20199 =
                                                       let uu____20202 =
                                                         let uu____20205 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1 in
                                                         FStar_List.append
                                                           [eqn] uu____20205 in
                                                       FStar_List.append
                                                         decls2 uu____20202 in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20199 in
                                                   FStar_List.append decls1
                                                     uu____20196 in
                                                 (uu____20193, env2))))))
                        | uu____20210 -> failwith "Impossible" in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20295 = varops.fresh "fuel" in
                          (uu____20295, FStar_SMTEncoding_Term.Fuel_sort) in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                        let env0 = env2 in
                        let uu____20298 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20386  ->
                                  fun uu____20387  ->
                                    match (uu____20386, uu____20387) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                        let g =
                                          let uu____20535 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented" in
                                          varops.new_fvar uu____20535 in
                                        let gtok =
                                          let uu____20537 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token" in
                                          varops.new_fvar uu____20537 in
                                        let env4 =
                                          let uu____20539 =
                                            let uu____20542 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm]) in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20542 in
                                          push_free_var env3 flid gtok
                                            uu____20539 in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2)) in
                        match uu____20298 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks in
                            let encode_one_binding env01 uu____20698 t_norm
                              uu____20700 =
                              match (uu____20698, uu____20700) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20744;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20745;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20773 =
                                    let uu____20780 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm] in
                                    match uu____20780 with
                                    | (tcenv',uu____20802,e_t) ->
                                        let uu____20808 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20819 ->
                                              failwith "Impossible" in
                                        (match uu____20808 with
                                         | (e1,t_norm1) ->
                                             ((let uu___409_20835 = env3 in
                                               {
                                                 bindings =
                                                   (uu___409_20835.bindings);
                                                 depth =
                                                   (uu___409_20835.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___409_20835.warn);
                                                 cache =
                                                   (uu___409_20835.cache);
                                                 nolabels =
                                                   (uu___409_20835.nolabels);
                                                 use_zfuel_name =
                                                   (uu___409_20835.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___409_20835.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___409_20835.current_module_name)
                                               }), e1, t_norm1)) in
                                  (match uu____20773 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____20850 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding") in
                                         if uu____20850
                                         then
                                           let uu____20851 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn in
                                           let uu____20852 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1 in
                                           let uu____20853 =
                                             FStar_Syntax_Print.term_to_string
                                               e1 in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____20851 uu____20852
                                             uu____20853
                                         else ());
                                        (let uu____20855 =
                                           destruct_bound_function flid
                                             t_norm1 e1 in
                                         match uu____20855 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____20892 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding") in
                                               if uu____20892
                                               then
                                                 let uu____20893 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders in
                                                 let uu____20894 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body in
                                                 let uu____20895 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals in
                                                 let uu____20896 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____20893 uu____20894
                                                   uu____20895 uu____20896
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____20900 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env' in
                                               match uu____20900 with
                                               | (vars,guards,env'1,binder_decls,uu____20931)
                                                   ->
                                                   let decl_g =
                                                     let uu____20945 =
                                                       let uu____20956 =
                                                         let uu____20959 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____20959 in
                                                       (g, uu____20956,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name")) in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____20945 in
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
                                                     let uu____20984 =
                                                       let uu____20991 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars in
                                                       (f, uu____20991) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____20984 in
                                                   let gsapp =
                                                     let uu____21001 =
                                                       let uu____21008 =
                                                         let uu____21011 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm]) in
                                                         uu____21011 ::
                                                           vars_tm in
                                                       (g, uu____21008) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21001 in
                                                   let gmax =
                                                     let uu____21017 =
                                                       let uu____21024 =
                                                         let uu____21027 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", []) in
                                                         uu____21027 ::
                                                           vars_tm in
                                                       (g, uu____21024) in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21017 in
                                                   let body1 =
                                                     let uu____21033 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1 in
                                                     if uu____21033
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body in
                                                   let uu____21035 =
                                                     encode_term body1 env'1 in
                                                   (match uu____21035 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21053 =
                                                            let uu____21060 =
                                                              let uu____21061
                                                                =
                                                                let uu____21076
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
                                                                  uu____21076) in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21061 in
                                                            let uu____21097 =
                                                              let uu____21100
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21100 in
                                                            (uu____21060,
                                                              uu____21097,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21053 in
                                                        let eqn_f =
                                                          let uu____21104 =
                                                            let uu____21111 =
                                                              let uu____21112
                                                                =
                                                                let uu____21123
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21123) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21112 in
                                                            (uu____21111,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21104 in
                                                        let eqn_g' =
                                                          let uu____21137 =
                                                            let uu____21144 =
                                                              let uu____21145
                                                                =
                                                                let uu____21156
                                                                  =
                                                                  let uu____21157
                                                                    =
                                                                    let uu____21162
                                                                    =
                                                                    let uu____21163
                                                                    =
                                                                    let uu____21170
                                                                    =
                                                                    let uu____21173
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21173
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21170) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21163 in
                                                                    (gsapp,
                                                                    uu____21162) in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21157 in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21156) in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21145 in
                                                            (uu____21144,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g)) in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21137 in
                                                        let uu____21196 =
                                                          let uu____21205 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02 in
                                                          match uu____21205
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21234)
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
                                                                  let uu____21259
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                  mk_Apply
                                                                    uu____21259
                                                                    (fuel ::
                                                                    vars1) in
                                                                let uu____21264
                                                                  =
                                                                  let uu____21271
                                                                    =
                                                                    let uu____21272
                                                                    =
                                                                    let uu____21283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21283) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21272 in
                                                                  (uu____21271,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21264 in
                                                              let uu____21304
                                                                =
                                                                let uu____21311
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp in
                                                                match uu____21311
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21324
                                                                    =
                                                                    let uu____21327
                                                                    =
                                                                    let uu____21328
                                                                    =
                                                                    let uu____21335
                                                                    =
                                                                    let uu____21336
                                                                    =
                                                                    let uu____21347
                                                                    =
                                                                    let uu____21348
                                                                    =
                                                                    let uu____21353
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21353,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21348 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21347) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21336 in
                                                                    (uu____21335,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21328 in
                                                                    [uu____21327] in
                                                                    (d3,
                                                                    uu____21324) in
                                                              (match uu____21304
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                        (match uu____21196
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
                            let uu____21418 =
                              let uu____21431 =
                                FStar_List.zip3 gtoks1 typs2 bindings1 in
                              FStar_List.fold_left
                                (fun uu____21510  ->
                                   fun uu____21511  ->
                                     match (uu____21510, uu____21511) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21666 =
                                           encode_one_binding env01 gtok ty
                                             lb in
                                         (match uu____21666 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21431 in
                            (match uu____21418 with
                             | (decls2,eqns,env01) ->
                                 let uu____21739 =
                                   let isDeclFun uu___375_21751 =
                                     match uu___375_21751 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21752 -> true
                                     | uu____21763 -> false in
                                   let uu____21764 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten in
                                   FStar_All.pipe_right uu____21764
                                     (FStar_List.partition isDeclFun) in
                                 (match uu____21739 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01))) in
                      let uu____21804 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___376_21808  ->
                                 match uu___376_21808 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21809 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21815 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21815))) in
                      if uu____21804
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
                   let uu____21867 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____21867
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
        let uu____21916 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____21916 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____21920 = encode_sigelt' env se in
      match uu____21920 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____21936 =
                  let uu____21937 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____21937 in
                [uu____21936]
            | uu____21938 ->
                let uu____21939 =
                  let uu____21942 =
                    let uu____21943 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21943 in
                  uu____21942 :: g in
                let uu____21944 =
                  let uu____21947 =
                    let uu____21948 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____21948 in
                  [uu____21947] in
                FStar_List.append uu____21939 uu____21944 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____21961 =
          let uu____21962 = FStar_Syntax_Subst.compress t in
          uu____21962.FStar_Syntax_Syntax.n in
        match uu____21961 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21966)) -> s = "opaque_to_smt"
        | uu____21967 -> false in
      let is_uninterpreted_by_smt t =
        let uu____21972 =
          let uu____21973 = FStar_Syntax_Subst.compress t in
          uu____21973.FStar_Syntax_Syntax.n in
        match uu____21972 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____21977)) -> s = "uninterpreted_by_smt"
        | uu____21978 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____21983 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____21988 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____21991 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____21994 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22009 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22013 =
            let uu____22014 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22014 Prims.op_Negation in
          if uu____22013
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22040 ->
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
               let uu____22060 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22060 with
               | (aname,atok,env2) ->
                   let uu____22076 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22076 with
                    | (formals,uu____22094) ->
                        let uu____22107 =
                          let uu____22112 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22112 env2 in
                        (match uu____22107 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22124 =
                                 let uu____22125 =
                                   let uu____22136 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22152  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22136,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22125 in
                               [uu____22124;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22165 =
                               let aux uu____22217 uu____22218 =
                                 match (uu____22217, uu____22218) with
                                 | ((bv,uu____22270),(env3,acc_sorts,acc)) ->
                                     let uu____22308 = gen_term_var env3 bv in
                                     (match uu____22308 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22165 with
                              | (uu____22380,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22403 =
                                      let uu____22410 =
                                        let uu____22411 =
                                          let uu____22422 =
                                            let uu____22423 =
                                              let uu____22428 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____22428) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22423 in
                                          ([[app]], xs_sorts, uu____22422) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22411 in
                                      (uu____22410,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22403 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____22448 =
                                      let uu____22455 =
                                        let uu____22456 =
                                          let uu____22467 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____22467) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22456 in
                                      (uu____22455,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22448 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____22486 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____22486 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22514,uu____22515)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22516 = new_term_constant_and_tok_from_lid env lid in
          (match uu____22516 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22533,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____22539 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___377_22543  ->
                      match uu___377_22543 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22544 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22549 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22550 -> false)) in
            Prims.op_Negation uu____22539 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____22559 =
               let uu____22566 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt) in
               encode_top_level_val uu____22566 env fv t quals in
             match uu____22559 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____22581 =
                   let uu____22584 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____22584 in
                 (uu____22581, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22592 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____22592 with
           | (uu____22601,f1) ->
               let uu____22603 = encode_formula f1 env in
               (match uu____22603 with
                | (f2,decls) ->
                    let g =
                      let uu____22617 =
                        let uu____22618 =
                          let uu____22625 =
                            let uu____22628 =
                              let uu____22629 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____22629 in
                            FStar_Pervasives_Native.Some uu____22628 in
                          let uu____22630 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____22625, uu____22630) in
                        FStar_SMTEncoding_Util.mkAssume uu____22618 in
                      [uu____22617] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22636) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____22648 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22666 =
                       let uu____22669 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____22669.FStar_Syntax_Syntax.fv_name in
                     uu____22666.FStar_Syntax_Syntax.v in
                   let uu____22670 =
                     let uu____22671 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____22671 in
                   if uu____22670
                   then
                     let val_decl =
                       let uu___412_22699 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___412_22699.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___412_22699.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___412_22699.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____22704 = encode_sigelt' env1 val_decl in
                     match uu____22704 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____22648 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22732,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22734;
                          FStar_Syntax_Syntax.lbtyp = uu____22735;
                          FStar_Syntax_Syntax.lbeff = uu____22736;
                          FStar_Syntax_Syntax.lbdef = uu____22737;_}::[]),uu____22738)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22757 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____22757 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____22786 =
                   let uu____22789 =
                     let uu____22790 =
                       let uu____22797 =
                         let uu____22798 =
                           let uu____22809 =
                             let uu____22810 =
                               let uu____22815 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____22815) in
                             FStar_SMTEncoding_Util.mkEq uu____22810 in
                           ([[b2t_x]], [xx], uu____22809) in
                         FStar_SMTEncoding_Util.mkForall uu____22798 in
                       (uu____22797,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____22790 in
                   [uu____22789] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22786 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____22848,uu____22849) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___378_22858  ->
                  match uu___378_22858 with
                  | FStar_Syntax_Syntax.Discriminator uu____22859 -> true
                  | uu____22860 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____22863,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____22874 =
                     let uu____22875 = FStar_List.hd l.FStar_Ident.ns in
                     uu____22875.FStar_Ident.idText in
                   uu____22874 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___379_22879  ->
                     match uu___379_22879 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____22880 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____22884) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___380_22901  ->
                  match uu___380_22901 with
                  | FStar_Syntax_Syntax.Projector uu____22902 -> true
                  | uu____22907 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____22910 = try_lookup_free_var env l in
          (match uu____22910 with
           | FStar_Pervasives_Native.Some uu____22917 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___413_22921 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___413_22921.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___413_22921.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___413_22921.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____22928) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____22946) ->
          let uu____22955 = encode_sigelts env ses in
          (match uu____22955 with
           | (g,env1) ->
               let uu____22972 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___381_22995  ->
                         match uu___381_22995 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____22996;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____22997;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____22998;_}
                             -> false
                         | uu____23001 -> true)) in
               (match uu____22972 with
                | (g',inversions) ->
                    let uu____23016 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___382_23037  ->
                              match uu___382_23037 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23038 ->
                                  true
                              | uu____23049 -> false)) in
                    (match uu____23016 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23067,tps,k,uu____23070,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___383_23087  ->
                    match uu___383_23087 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23088 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23097 = c in
              match uu____23097 with
              | (name,args,uu____23102,uu____23103,uu____23104) ->
                  let uu____23109 =
                    let uu____23110 =
                      let uu____23121 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23138  ->
                                match uu____23138 with
                                | (uu____23145,sort,uu____23147) -> sort)) in
                      (name, uu____23121, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23110 in
                  [uu____23109]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23174 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23180 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23180 FStar_Option.isNone)) in
            if uu____23174
            then []
            else
              (let uu____23212 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23212 with
               | (xxsym,xx) ->
                   let uu____23221 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23260  ->
                             fun l  ->
                               match uu____23260 with
                               | (out,decls) ->
                                   let uu____23280 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23280 with
                                    | (uu____23291,data_t) ->
                                        let uu____23293 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23293 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23339 =
                                                 let uu____23340 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23340.FStar_Syntax_Syntax.n in
                                               match uu____23339 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23351,indices) ->
                                                   indices
                                               | uu____23373 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23397  ->
                                                         match uu____23397
                                                         with
                                                         | (x,uu____23403) ->
                                                             let uu____23404
                                                               =
                                                               let uu____23405
                                                                 =
                                                                 let uu____23412
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____23412,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23405 in
                                                             push_term_var
                                                               env1 x
                                                               uu____23404)
                                                    env) in
                                             let uu____23415 =
                                               encode_args indices env1 in
                                             (match uu____23415 with
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
                                                      let uu____23441 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23457
                                                                 =
                                                                 let uu____23462
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____23462,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23457)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____23441
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____23465 =
                                                      let uu____23466 =
                                                        let uu____23471 =
                                                          let uu____23472 =
                                                            let uu____23477 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____23477,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23472 in
                                                        (out, uu____23471) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23466 in
                                                    (uu____23465,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23221 with
                    | (data_ax,decls) ->
                        let uu____23490 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____23490 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23501 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23501 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____23505 =
                                 let uu____23512 =
                                   let uu____23513 =
                                     let uu____23524 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____23539 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____23524,
                                       uu____23539) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23513 in
                                 let uu____23554 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____23512,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23554) in
                               FStar_SMTEncoding_Util.mkAssume uu____23505 in
                             FStar_List.append decls [fuel_guarded_inversion]))) in
          let uu____23557 =
            let uu____23570 =
              let uu____23571 = FStar_Syntax_Subst.compress k in
              uu____23571.FStar_Syntax_Syntax.n in
            match uu____23570 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23616 -> (tps, k) in
          (match uu____23557 with
           | (formals,res) ->
               let uu____23639 = FStar_Syntax_Subst.open_term formals res in
               (match uu____23639 with
                | (formals1,res1) ->
                    let uu____23650 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____23650 with
                     | (vars,guards,env',binder_decls,uu____23675) ->
                         let uu____23688 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____23688 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____23707 =
                                  let uu____23714 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____23714) in
                                FStar_SMTEncoding_Util.mkApp uu____23707 in
                              let uu____23723 =
                                let tname_decl =
                                  let uu____23733 =
                                    let uu____23734 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23766  ->
                                              match uu____23766 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____23779 = varops.next_id () in
                                    (tname, uu____23734,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23779, false) in
                                  constructor_or_logic_type_decl uu____23733 in
                                let uu____23788 =
                                  match vars with
                                  | [] ->
                                      let uu____23801 =
                                        let uu____23802 =
                                          let uu____23805 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23805 in
                                        push_free_var env1 t tname
                                          uu____23802 in
                                      ([], uu____23801)
                                  | uu____23812 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____23821 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23821 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____23835 =
                                          let uu____23842 =
                                            let uu____23843 =
                                              let uu____23858 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____23858) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____23843 in
                                          (uu____23842,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23835 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____23788 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____23723 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____23898 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____23898 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____23916 =
                                               let uu____23917 =
                                                 let uu____23924 =
                                                   let uu____23925 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____23925 in
                                                 (uu____23924,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23917 in
                                             [uu____23916]
                                           else [] in
                                         let uu____23929 =
                                           let uu____23932 =
                                             let uu____23935 =
                                               let uu____23936 =
                                                 let uu____23943 =
                                                   let uu____23944 =
                                                     let uu____23955 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____23955) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____23944 in
                                                 (uu____23943,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____23936 in
                                             [uu____23935] in
                                           FStar_List.append karr uu____23932 in
                                         FStar_List.append decls1 uu____23929 in
                                   let aux =
                                     let uu____23971 =
                                       let uu____23974 =
                                         inversion_axioms tapp vars in
                                       let uu____23977 =
                                         let uu____23980 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____23980] in
                                       FStar_List.append uu____23974
                                         uu____23977 in
                                     FStar_List.append kindingAx uu____23971 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23987,uu____23988,uu____23989,uu____23990,uu____23991)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____23999,t,uu____24001,n_tps,uu____24003) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24011 = new_term_constant_and_tok_from_lid env d in
          (match uu____24011 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24028 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24028 with
                | (formals,t_res) ->
                    let uu____24063 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24063 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24077 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24077 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24147 =
                                            mk_term_projector_name d x in
                                          (uu____24147,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24149 =
                                  let uu____24168 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24168, true) in
                                FStar_All.pipe_right uu____24149
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
                              let uu____24207 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24207 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24219::uu____24220 ->
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
                                         let uu____24265 =
                                           let uu____24276 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24276) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24265
                                     | uu____24301 -> tok_typing in
                                   let uu____24310 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____24310 with
                                    | (vars',guards',env'',decls_formals,uu____24335)
                                        ->
                                        let uu____24348 =
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
                                        (match uu____24348 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24379 ->
                                                   let uu____24386 =
                                                     let uu____24387 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24387 in
                                                   [uu____24386] in
                                             let encode_elim uu____24397 =
                                               let uu____24398 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____24398 with
                                               | (head1,args) ->
                                                   let uu____24441 =
                                                     let uu____24442 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____24442.FStar_Syntax_Syntax.n in
                                                   (match uu____24441 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24452;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24453;_},uu____24454)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____24460 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____24460
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
                                                                 | uu____24503
                                                                    ->
                                                                    let uu____24504
                                                                    =
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
                                                                    (uu____24510,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____24505 in
                                                                    FStar_Exn.raise
                                                                    uu____24504 in
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
                                                                    let uu____25044
                                                                    =
                                                                    let uu____25049
                                                                    =
                                                                    let uu____25050
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25050 in
                                                                    (uu____25049,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25044 in
                                                                    FStar_Exn.raise
                                                                    uu____25043 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25066
                                                                    =
                                                                    let uu____25067
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25067 in
                                                                    if
                                                                    uu____25066
                                                                    then
                                                                    let uu____25080
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25080]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25082
                                                               =
                                                               let uu____25095
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25145
                                                                     ->
                                                                    fun
                                                                    uu____25146
                                                                     ->
                                                                    match 
                                                                    (uu____25145,
                                                                    uu____25146)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25241
                                                                    =
                                                                    let uu____25248
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25248 in
                                                                    (match uu____25241
                                                                    with
                                                                    | 
                                                                    (uu____25261,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25269
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25269
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25271
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25271
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
                                                                 uu____25095 in
                                                             (match uu____25082
                                                              with
                                                              | (uu____25286,arg_vars,elim_eqns_or_guards,uu____25289)
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
                                                                    let uu____25319
                                                                    =
                                                                    let uu____25326
                                                                    =
                                                                    let uu____25327
                                                                    =
                                                                    let uu____25338
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25349
                                                                    =
                                                                    let uu____25350
                                                                    =
                                                                    let uu____25355
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25355) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25350 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25338,
                                                                    uu____25349) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25327 in
                                                                    (uu____25326,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25319 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25378
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25378,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25380
                                                                    =
                                                                    let uu____25387
                                                                    =
                                                                    let uu____25388
                                                                    =
                                                                    let uu____25399
                                                                    =
                                                                    let uu____25404
                                                                    =
                                                                    let uu____25407
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25407] in
                                                                    [uu____25404] in
                                                                    let uu____25412
                                                                    =
                                                                    let uu____25413
                                                                    =
                                                                    let uu____25418
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25419
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25418,
                                                                    uu____25419) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25413 in
                                                                    (uu____25399,
                                                                    [x],
                                                                    uu____25412) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25388 in
                                                                    let uu____25438
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25387,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25438) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25380
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25445
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
                                                                    (let uu____25473
                                                                    =
                                                                    let uu____25474
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25474
                                                                    dapp1 in
                                                                    [uu____25473]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25445
                                                                    FStar_List.flatten in
                                                                    let uu____25481
                                                                    =
                                                                    let uu____25488
                                                                    =
                                                                    let uu____25489
                                                                    =
                                                                    let uu____25500
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25511
                                                                    =
                                                                    let uu____25512
                                                                    =
                                                                    let uu____25517
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25517) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25512 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25500,
                                                                    uu____25511) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25489 in
                                                                    (uu____25488,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25481) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25536 ->
                                                        ((let uu____25538 =
                                                            let uu____25539 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____25540 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25539
                                                              uu____25540 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25538);
                                                         ([], []))) in
                                             let uu____25545 = encode_elim () in
                                             (match uu____25545 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25565 =
                                                      let uu____25568 =
                                                        let uu____25571 =
                                                          let uu____25574 =
                                                            let uu____25577 =
                                                              let uu____25578
                                                                =
                                                                let uu____25589
                                                                  =
                                                                  let uu____25592
                                                                    =
                                                                    let uu____25593
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25593 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25592 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25589) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25578 in
                                                            [uu____25577] in
                                                          let uu____25598 =
                                                            let uu____25601 =
                                                              let uu____25604
                                                                =
                                                                let uu____25607
                                                                  =
                                                                  let uu____25610
                                                                    =
                                                                    let uu____25613
                                                                    =
                                                                    let uu____25616
                                                                    =
                                                                    let uu____25617
                                                                    =
                                                                    let uu____25624
                                                                    =
                                                                    let uu____25625
                                                                    =
                                                                    let uu____25636
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25636) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25625 in
                                                                    (uu____25624,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25617 in
                                                                    let uu____25649
                                                                    =
                                                                    let uu____25652
                                                                    =
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25660
                                                                    =
                                                                    let uu____25661
                                                                    =
                                                                    let uu____25672
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____25683
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25672,
                                                                    uu____25683) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25661 in
                                                                    (uu____25660,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25653 in
                                                                    [uu____25652] in
                                                                    uu____25616
                                                                    ::
                                                                    uu____25649 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25613 in
                                                                  FStar_List.append
                                                                    uu____25610
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25607 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25604 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25601 in
                                                          FStar_List.append
                                                            uu____25574
                                                            uu____25598 in
                                                        FStar_List.append
                                                          decls3 uu____25571 in
                                                      FStar_List.append
                                                        decls2 uu____25568 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25565 in
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
           (fun uu____25729  ->
              fun se  ->
                match uu____25729 with
                | (g,env1) ->
                    let uu____25749 = encode_sigelt env1 se in
                    (match uu____25749 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25806 =
        match uu____25806 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____25838 ->
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
                 ((let uu____25844 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____25844
                   then
                     let uu____25845 = FStar_Syntax_Print.bv_to_string x in
                     let uu____25846 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____25847 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____25845 uu____25846 uu____25847
                   else ());
                  (let uu____25849 = encode_term t1 env1 in
                   match uu____25849 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____25865 =
                         let uu____25872 =
                           let uu____25873 =
                             let uu____25874 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____25874
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____25873 in
                         new_term_constant_from_string env1 x uu____25872 in
                       (match uu____25865 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____25890 = FStar_Options.log_queries () in
                              if uu____25890
                              then
                                let uu____25893 =
                                  let uu____25894 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____25895 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____25896 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____25894 uu____25895 uu____25896 in
                                FStar_Pervasives_Native.Some uu____25893
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____25912,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____25926 = encode_free_var false env1 fv t t_norm [] in
                 (match uu____25926 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____25949,se,uu____25951) ->
                 let uu____25956 = encode_sigelt env1 se in
                 (match uu____25956 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____25973,se) ->
                 let uu____25979 = encode_sigelt env1 se in
                 (match uu____25979 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____25996 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____25996 with | (uu____26019,decls,env1) -> (decls, env1)
let encode_labels:
  'Auu____26031 'Auu____26032 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26032,'Auu____26031)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26100  ->
              match uu____26100 with
              | (l,uu____26112,uu____26113) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None))) in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26159  ->
              match uu____26159 with
              | (l,uu____26173,uu____26174) ->
                  let uu____26183 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l) in
                  let uu____26184 =
                    let uu____26187 =
                      let uu____26188 = FStar_SMTEncoding_Util.mkFreeV l in
                      FStar_SMTEncoding_Term.Eval uu____26188 in
                    [uu____26187] in
                  uu____26183 :: uu____26184)) in
    (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26209 =
      let uu____26212 =
        let uu____26213 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26216 =
          let uu____26217 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26217 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26213;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26216
        } in
      [uu____26212] in
    FStar_ST.op_Colon_Equals last_env uu____26209
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26274 = FStar_ST.op_Bang last_env in
      match uu____26274 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26328 ->
          let uu___414_26331 = e in
          let uu____26332 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___414_26331.bindings);
            depth = (uu___414_26331.depth);
            tcenv;
            warn = (uu___414_26331.warn);
            cache = (uu___414_26331.cache);
            nolabels = (uu___414_26331.nolabels);
            use_zfuel_name = (uu___414_26331.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___414_26331.encode_non_total_function_typ);
            current_module_name = uu____26332
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26336 = FStar_ST.op_Bang last_env in
    match uu____26336 with
    | [] -> failwith "Empty env stack"
    | uu____26389::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26445  ->
    let uu____26446 = FStar_ST.op_Bang last_env in
    match uu____26446 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___415_26507 = hd1 in
          {
            bindings = (uu___415_26507.bindings);
            depth = (uu___415_26507.depth);
            tcenv = (uu___415_26507.tcenv);
            warn = (uu___415_26507.warn);
            cache = refs;
            nolabels = (uu___415_26507.nolabels);
            use_zfuel_name = (uu___415_26507.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___415_26507.encode_non_total_function_typ);
            current_module_name = (uu___415_26507.current_module_name)
          } in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26560  ->
    let uu____26561 = FStar_ST.op_Bang last_env in
    match uu____26561 with
    | [] -> failwith "Popping an empty stack"
    | uu____26614::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
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
        | (uu____26705::uu____26706,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___416_26714 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___416_26714.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___416_26714.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___416_26714.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26715 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26730 =
        let uu____26733 =
          let uu____26734 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____26734 in
        let uu____26735 = open_fact_db_tags env in uu____26733 :: uu____26735 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26730
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
      let uu____26757 = encode_sigelt env se in
      match uu____26757 with
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
        let uu____26793 = FStar_Options.log_queries () in
        if uu____26793
        then
          let uu____26796 =
            let uu____26797 =
              let uu____26798 =
                let uu____26799 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____26799 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____26798 in
            FStar_SMTEncoding_Term.Caption uu____26797 in
          uu____26796 :: decls
        else decls in
      (let uu____26810 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26810
       then
         let uu____26811 = FStar_Syntax_Print.sigelt_to_string se in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26811
       else ());
      (let env =
         let uu____26814 = FStar_TypeChecker_Env.current_module tcenv in
         get_env uu____26814 tcenv in
       let uu____26815 = encode_top_level_facts env se in
       match uu____26815 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26829 = caption decls in
             FStar_SMTEncoding_Z3.giveZ3 uu____26829)))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____26841 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____26841
       then
         let uu____26842 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26842
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26877  ->
                 fun se  ->
                   match uu____26877 with
                   | (g,env2) ->
                       let uu____26897 = encode_top_level_facts env2 se in
                       (match uu____26897 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____26920 =
         encode_signature
           (let uu___417_26929 = env in
            {
              bindings = (uu___417_26929.bindings);
              depth = (uu___417_26929.depth);
              tcenv = (uu___417_26929.tcenv);
              warn = false;
              cache = (uu___417_26929.cache);
              nolabels = (uu___417_26929.nolabels);
              use_zfuel_name = (uu___417_26929.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___417_26929.encode_non_total_function_typ);
              current_module_name = (uu___417_26929.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____26920 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26946 = FStar_Options.log_queries () in
             if uu____26946
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___418_26954 = env1 in
               {
                 bindings = (uu___418_26954.bindings);
                 depth = (uu___418_26954.depth);
                 tcenv = (uu___418_26954.tcenv);
                 warn = true;
                 cache = (uu___418_26954.cache);
                 nolabels = (uu___418_26954.nolabels);
                 use_zfuel_name = (uu___418_26954.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___418_26954.encode_non_total_function_typ);
                 current_module_name = (uu___418_26954.current_module_name)
               });
            (let uu____26956 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____26956
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
        (let uu____27008 =
           let uu____27009 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27009.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27008);
        (let env =
           let uu____27011 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27011 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27023 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27058 = aux rest in
                 (match uu____27058 with
                  | (out,rest1) ->
                      let t =
                        let uu____27088 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27088 with
                        | FStar_Pervasives_Native.Some uu____27093 ->
                            let uu____27094 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit in
                            FStar_Syntax_Util.refine uu____27094
                              x.FStar_Syntax_Syntax.sort
                        | uu____27095 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27099 =
                        let uu____27102 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___419_27105 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___419_27105.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___419_27105.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27102 :: out in
                      (uu____27099, rest1))
             | uu____27110 -> ([], bindings1) in
           let uu____27117 = aux bindings in
           match uu____27117 with
           | (closing,bindings1) ->
               let uu____27142 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27142, bindings1) in
         match uu____27023 with
         | (q1,bindings1) ->
             let uu____27165 =
               let uu____27170 =
                 FStar_List.filter
                   (fun uu___384_27175  ->
                      match uu___384_27175 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27176 ->
                          false
                      | uu____27183 -> true) bindings1 in
               encode_env_bindings env uu____27170 in
             (match uu____27165 with
              | (env_decls,env1) ->
                  ((let uu____27201 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27201
                    then
                      let uu____27202 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27202
                    else ());
                   (let uu____27204 = encode_formula q1 env1 in
                    match uu____27204 with
                    | (phi,qdecls) ->
                        let uu____27225 =
                          let uu____27230 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27230 phi in
                        (match uu____27225 with
                         | (labels,phi1) ->
                             let uu____27247 = encode_labels labels in
                             (match uu____27247 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27284 =
                                      let uu____27291 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27292 =
                                        varops.mk_unique "@query" in
                                      (uu____27291,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27292) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27284 in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"]) in
                                  (query_prelude, labels, qry, suffix)))))))