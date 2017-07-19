open Prims
let add_fuel x tl1 =
  let uu____22 = FStar_Options.unthrottle_inductives () in
  if uu____22 then tl1 else x :: tl1
let withenv c uu____56 = match uu____56 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___102_119  ->
       match uu___102_119 with
       | (FStar_Util.Inl uu____128,uu____129) -> false
       | uu____134 -> true) args
let subst_lcomp_opt s l =
  match l with
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
      let uu____185 =
        let uu____190 =
          let uu____191 =
            let uu____196 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____196 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191 in
        FStar_Util.Inl uu____190 in
      FStar_Pervasives_Native.Some uu____185
  | uu____205 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_225 = a in
        let uu____226 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____226;
          FStar_Syntax_Syntax.index =
            (uu___126_225.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_225.FStar_Syntax_Syntax.sort)
        } in
      let uu____227 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____227
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____243 =
          let uu____244 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____244 in
        let uu____245 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____245 with
        | (uu____250,t) ->
            let uu____252 =
              let uu____253 = FStar_Syntax_Subst.compress t in
              uu____253.FStar_Syntax_Syntax.n in
            (match uu____252 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____280 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____280 with
                  | (binders,uu____286) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____301 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____310 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____310
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____319 =
        let uu____324 = mk_term_projector_name lid a in
        (uu____324,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____319
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____333 =
        let uu____338 = mk_term_projector_name_by_pos lid i in
        (uu____338,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____333
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let __proj__Mkvarops_t__item__push: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
let __proj__Mkvarops_t__item__pop: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
let __proj__Mkvarops_t__item__mark: varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mark
let __proj__Mkvarops_t__item__reset_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__reset_mark
let __proj__Mkvarops_t__item__commit_mark:
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__commit_mark
let __proj__Mkvarops_t__item__new_var:
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
let __proj__Mkvarops_t__item__new_fvar:
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
let __proj__Mkvarops_t__item__fresh: varops_t -> Prims.string -> Prims.string
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
let __proj__Mkvarops_t__item__string_const:
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
let __proj__Mkvarops_t__item__next_id: varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
let __proj__Mkvarops_t__item__mk_unique:
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____956 =
    let uu____957 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____960 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____957, uu____960) in
  let scopes =
    let uu____980 = let uu____991 = new_scope () in [uu____991] in
    FStar_Util.mk_ref uu____980 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____1032 =
        let uu____1035 = FStar_ST.read scopes in
        FStar_Util.find_map uu____1035
          (fun uu____1069  ->
             match uu____1069 with
             | (names1,uu____1081) -> FStar_Util.smap_try_find names1 y1) in
      match uu____1032 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1090 ->
          (FStar_Util.incr ctr;
           (let uu____1095 =
              let uu____1096 =
                let uu____1097 = FStar_ST.read ctr in
                Prims.string_of_int uu____1097 in
              Prims.strcat "__" uu____1096 in
            Prims.strcat y1 uu____1095)) in
    let top_scope =
      let uu____1103 =
        let uu____1112 = FStar_ST.read scopes in FStar_List.hd uu____1112 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1103 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1172 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____1183 =
      let uu____1184 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1184 in
    FStar_Util.format2 "%s_%s" pfx uu____1183 in
  let string_const s =
    let uu____1189 =
      let uu____1192 = FStar_ST.read scopes in
      FStar_Util.find_map uu____1192
        (fun uu____1226  ->
           match uu____1226 with
           | (uu____1237,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1189 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1250 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1250 in
        let top_scope =
          let uu____1254 =
            let uu____1263 = FStar_ST.read scopes in FStar_List.hd uu____1263 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1254 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1312 =
    let uu____1313 =
      let uu____1324 = new_scope () in
      let uu____1333 = FStar_ST.read scopes in uu____1324 :: uu____1333 in
    FStar_ST.write scopes uu____1313 in
  let pop1 uu____1379 =
    let uu____1380 =
      let uu____1391 = FStar_ST.read scopes in FStar_List.tl uu____1391 in
    FStar_ST.write scopes uu____1380 in
  let mark1 uu____1437 = push1 () in
  let reset_mark1 uu____1441 = pop1 () in
  let commit_mark1 uu____1445 =
    let uu____1446 = FStar_ST.read scopes in
    match uu____1446 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____1554 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___127_1569 = x in
    let uu____1570 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1570;
      FStar_Syntax_Syntax.index = (uu___127_1569.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1569.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1604 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1642 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
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
  current_module_name: Prims.string;}
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
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___103_2042  ->
            match uu___103_2042 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____2046 -> [])) in
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
    let uu____2057 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_2067  ->
              match uu___104_2067 with
              | Binding_var (x,uu____2069) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2071,uu____2072,uu____2073) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____2057 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2120 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____2120
      then
        let uu____2123 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____2123
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
      let uu____2138 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____2138)
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
        (let uu___128_2156 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_2156.tcenv);
           warn = (uu___128_2156.warn);
           cache = (uu___128_2156.cache);
           nolabels = (uu___128_2156.nolabels);
           use_zfuel_name = (uu___128_2156.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_2156.encode_non_total_function_typ);
           current_module_name = (uu___128_2156.current_module_name)
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
        (let uu___129_2176 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_2176.depth);
           tcenv = (uu___129_2176.tcenv);
           warn = (uu___129_2176.warn);
           cache = (uu___129_2176.cache);
           nolabels = (uu___129_2176.nolabels);
           use_zfuel_name = (uu___129_2176.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_2176.encode_non_total_function_typ);
           current_module_name = (uu___129_2176.current_module_name)
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
          (let uu___130_2200 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_2200.depth);
             tcenv = (uu___130_2200.tcenv);
             warn = (uu___130_2200.warn);
             cache = (uu___130_2200.cache);
             nolabels = (uu___130_2200.nolabels);
             use_zfuel_name = (uu___130_2200.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_2200.encode_non_total_function_typ);
             current_module_name = (uu___130_2200.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_2213 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_2213.depth);
          tcenv = (uu___131_2213.tcenv);
          warn = (uu___131_2213.warn);
          cache = (uu___131_2213.cache);
          nolabels = (uu___131_2213.nolabels);
          use_zfuel_name = (uu___131_2213.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_2213.encode_non_total_function_typ);
          current_module_name = (uu___131_2213.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_2239  ->
             match uu___105_2239 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2252 -> FStar_Pervasives_Native.None) in
      let uu____2257 = aux a in
      match uu____2257 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____2269 = aux a2 in
          (match uu____2269 with
           | FStar_Pervasives_Native.None  ->
               let uu____2280 =
                 let uu____2281 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____2282 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2281 uu____2282 in
               failwith uu____2280
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
      let uu____2311 =
        let uu___132_2312 = env in
        let uu____2313 =
          let uu____2316 =
            let uu____2317 =
              let uu____2330 =
                let uu____2333 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                  uu____2333 in
              (x, fname, uu____2330, FStar_Pervasives_Native.None) in
            Binding_fvar uu____2317 in
          uu____2316 :: (env.bindings) in
        {
          bindings = uu____2313;
          depth = (uu___132_2312.depth);
          tcenv = (uu___132_2312.tcenv);
          warn = (uu___132_2312.warn);
          cache = (uu___132_2312.cache);
          nolabels = (uu___132_2312.nolabels);
          use_zfuel_name = (uu___132_2312.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_2312.encode_non_total_function_typ);
          current_module_name = (uu___132_2312.current_module_name)
        } in
      (fname, ftok, uu____2311)
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
        (fun uu___106_2377  ->
           match uu___106_2377 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2416 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2435 =
        lookup_binding env
          (fun uu___107_2443  ->
             match uu___107_2443 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2458 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____2435 FStar_Option.isSome
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
      let uu____2479 = try_lookup_lid env a in
      match uu____2479 with
      | FStar_Pervasives_Native.None  ->
          let uu____2512 =
            let uu____2513 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____2513 in
          failwith uu____2512
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
          let uu___133_2565 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_2565.depth);
            tcenv = (uu___133_2565.tcenv);
            warn = (uu___133_2565.warn);
            cache = (uu___133_2565.cache);
            nolabels = (uu___133_2565.nolabels);
            use_zfuel_name = (uu___133_2565.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_2565.encode_non_total_function_typ);
            current_module_name = (uu___133_2565.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2582 = lookup_lid env x in
        match uu____2582 with
        | (t1,t2,uu____2595) ->
            let t3 =
              let uu____2605 =
                let uu____2612 =
                  let uu____2615 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2615] in
                (f, uu____2612) in
              FStar_SMTEncoding_Util.mkApp uu____2605 in
            let uu___134_2620 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_2620.depth);
              tcenv = (uu___134_2620.tcenv);
              warn = (uu___134_2620.warn);
              cache = (uu___134_2620.cache);
              nolabels = (uu___134_2620.nolabels);
              use_zfuel_name = (uu___134_2620.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_2620.encode_non_total_function_typ);
              current_module_name = (uu___134_2620.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2635 = try_lookup_lid env l in
      match uu____2635 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2684 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2692,fuel::[]) ->
                         let uu____2696 =
                           let uu____2697 =
                             let uu____2698 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2698
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2697 "fuel" in
                         if uu____2696
                         then
                           let uu____2701 =
                             let uu____2702 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2702
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2701
                         else FStar_Pervasives_Native.Some t
                     | uu____2706 -> FStar_Pervasives_Native.Some t)
                | uu____2707 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2722 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2722 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2726 =
            let uu____2727 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2727 in
          failwith uu____2726
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2740 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2740 with | (x,uu____2752,uu____2753) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2780 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2780 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2816;
                 FStar_SMTEncoding_Term.rng = uu____2817;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2832 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2856 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___108_2874  ->
           match uu___108_2874 with
           | Binding_fvar (uu____2877,nm',tok,uu____2880) when nm = nm' ->
               tok
           | uu____2889 -> FStar_Pervasives_Native.None)
let mkForall_fuel' n1 uu____2914 =
  match uu____2914 with
  | (pats,vars,body) ->
      let fallback uu____2939 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2944 = FStar_Options.unthrottle_inductives () in
      if uu____2944
      then fallback ()
      else
        (let uu____2946 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2946 with
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
                       | uu____2977 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2998 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2998
                     | uu____3001 ->
                         let uu____3002 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____3002 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____3007 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____3051 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3066 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3075 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3076 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3097 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3116 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3118 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3118 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____3136;
             FStar_Syntax_Syntax.pos = uu____3137;
             FStar_Syntax_Syntax.vars = uu____3138;_},uu____3139)
          ->
          let uu____3168 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3168 FStar_Option.isNone
      | uu____3185 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3194 =
        let uu____3195 = FStar_Syntax_Util.un_uinst t in
        uu____3195.FStar_Syntax_Syntax.n in
      match uu____3194 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3200,uu____3201,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_3226  ->
                  match uu___109_3226 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3227 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3229 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____3229 FStar_Option.isSome
      | uu____3246 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3255 = head_normal env t in
      if uu____3255
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
    let uu____3269 =
      let uu____3270 = FStar_Syntax_Syntax.null_binder t in [uu____3270] in
    let uu____3271 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____3269 uu____3271 FStar_Pervasives_Native.None
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
                    let uu____3311 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3311
                | s ->
                    let uu____3316 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3316) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_3334  ->
    match uu___110_3334 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3335 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____3374;
                       FStar_SMTEncoding_Term.rng = uu____3375;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3398) ->
              let uu____3407 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3418 -> false) args (FStar_List.rev xs)) in
              if uu____3407
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3422,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____3426 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3430 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____3430)) in
              if uu____3426
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3434 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
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
        FStar_Pervasives_Native.tuple2 Prims.list;}
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
    | uu____3664 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_3668  ->
    match uu___111_3668 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____3670 =
          let uu____3677 =
            let uu____3680 =
              let uu____3681 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____3681 in
            [uu____3680] in
          ("FStar.Char.Char", uu____3677) in
        FStar_SMTEncoding_Util.mkApp uu____3670
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____3695 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____3695
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____3697) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____3713) ->
        let uu____3718 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____3718
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____3723 =
          let uu____3724 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____3724 in
        failwith uu____3723
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3749 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3764 ->
            let uu____3773 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____3773
        | uu____3774 ->
            if norm1
            then let uu____3775 = whnf env t1 in aux false uu____3775
            else
              (let uu____3777 =
                 let uu____3778 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____3779 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3778 uu____3779 in
               failwith uu____3777) in
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
    | uu____3815 ->
        let uu____3816 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3816)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3860::uu____3861::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3865::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____3868 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3890 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3906 -> failwith "Expected an Integer term"
let is_BitVector_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar
     fv,(sz_arg,uu____3968)::uu____3969::uu____3970::[]) ->
      (((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid)
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_xor_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_shift_left_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_shift_right_lid))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid))
           ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4039)::uu____4040::[]) ->
      ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) ||
         (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | uu____4091 -> false
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
        (let uu____4306 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____4306
         then
           let uu____4307 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____4307
         else ());
        (let uu____4309 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4393  ->
                   fun b  ->
                     match uu____4393 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4472 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____4488 = gen_term_var env1 x in
                           match uu____4488 with
                           | (xxsym,xx,env') ->
                               let uu____4512 =
                                 let uu____4517 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____4517 env1 xx in
                               (match uu____4512 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____4472 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____4309 with
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
          let uu____4676 = encode_term t env in
          match uu____4676 with
          | (t1,decls) ->
              let uu____4687 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____4687, decls)
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
          let uu____4698 = encode_term t env in
          match uu____4698 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4713 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____4713, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4715 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____4715, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4723 = encode_args args_e env in
        match uu____4723 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4742 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____4751 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____4751 in
            let binary arg_tms1 =
              let uu____4764 =
                let uu____4765 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____4765 in
              let uu____4766 =
                let uu____4767 =
                  let uu____4768 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____4768 in
                FStar_SMTEncoding_Term.unboxInt uu____4767 in
              (uu____4764, uu____4766) in
            let mk_default uu____4774 =
              let uu____4775 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____4775 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____4826 = FStar_Options.smtencoding_l_arith_native () in
              if uu____4826
              then
                let uu____4827 = let uu____4828 = mk_args ts in op uu____4828 in
                FStar_All.pipe_right uu____4827 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____4857 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____4857
              then
                let uu____4858 = binary ts in
                match uu____4858 with
                | (t1,t2) ->
                    let uu____4865 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____4865
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4869 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____4869
                 then
                   let uu____4870 = op (binary ts) in
                   FStar_All.pipe_right uu____4870
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
            let uu____5001 =
              let uu____5010 =
                FStar_List.tryFind
                  (fun uu____5032  ->
                     match uu____5032 with
                     | (l,uu____5042) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____5010 FStar_Util.must in
            (match uu____5001 with
             | (uu____5081,op) ->
                 let uu____5091 = op arg_tms in (uu____5091, decls))
and encode_BitVector_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5101 = FStar_List.hd args_e in
        match uu____5101 with
        | (tm_sz,uu____5109) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____5123 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____5123 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____5131 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____5131);
                   t_decls) in
            let uu____5132 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5152::(sz_arg,uu____5154)::uu____5155::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5222 =
                    let uu____5225 = FStar_List.tail args_e in
                    FStar_List.tail uu____5225 in
                  let uu____5228 =
                    let uu____5231 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____5231 in
                  (uu____5222, uu____5228)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5237::(sz_arg,uu____5239)::uu____5240::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5307 =
                    let uu____5308 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5308 in
                  failwith uu____5307
              | uu____5317 ->
                  let uu____5324 = FStar_List.tail args_e in
                  (uu____5324, FStar_Pervasives_Native.None) in
            (match uu____5132 with
             | (arg_tms,ext_sz) ->
                 let uu____5347 = encode_args arg_tms env in
                 (match uu____5347 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5368 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____5377 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5377 in
                      let unary_arith arg_tms2 =
                        let uu____5386 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____5386 in
                      let binary arg_tms2 =
                        let uu____5399 =
                          let uu____5400 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5400 in
                        let uu____5401 =
                          let uu____5402 =
                            let uu____5403 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5403 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5402 in
                        (uu____5399, uu____5401) in
                      let binary_arith arg_tms2 =
                        let uu____5418 =
                          let uu____5419 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5419 in
                        let uu____5420 =
                          let uu____5421 =
                            let uu____5422 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____5422 in
                          FStar_SMTEncoding_Term.unboxInt uu____5421 in
                        (uu____5418, uu____5420) in
                      let mk_bv op mk_args resBox ts =
                        let uu____5471 =
                          let uu____5472 = mk_args ts in op uu____5472 in
                        FStar_All.pipe_right uu____5471 resBox in
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
                        let uu____5562 =
                          let uu____5565 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____5565 in
                        let uu____5567 =
                          let uu____5570 =
                            let uu____5571 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____5571 in
                          FStar_SMTEncoding_Term.boxBitVec uu____5570 in
                        mk_bv uu____5562 unary uu____5567 arg_tms2 in
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
                      let uu____5746 =
                        let uu____5755 =
                          FStar_List.tryFind
                            (fun uu____5777  ->
                               match uu____5777 with
                               | (l,uu____5787) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____5755 FStar_Util.must in
                      (match uu____5746 with
                       | (uu____5828,op) ->
                           let uu____5838 = op arg_tms1 in
                           (uu____5838, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____5849 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____5849
       then
         let uu____5850 = FStar_Syntax_Print.tag_of_term t in
         let uu____5851 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____5852 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5850 uu____5851
           uu____5852
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5858 ->
           let uu____5887 =
             let uu____5888 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5889 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5890 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5891 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5888
               uu____5889 uu____5890 uu____5891 in
           failwith uu____5887
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5896 =
             let uu____5897 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____5898 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____5899 = FStar_Syntax_Print.term_to_string t0 in
             let uu____5900 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5897
               uu____5898 uu____5899 uu____5900 in
           failwith uu____5896
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5906 =
             let uu____5907 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5907 in
           failwith uu____5906
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____5914) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5972) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5986 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____5986, [])
       | FStar_Syntax_Syntax.Tm_type uu____5989 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5993) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6003 = encode_const c in (uu____6003, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____6029 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____6029 with
            | (binders1,res) ->
                let uu____6040 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____6040
                then
                  let uu____6045 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____6045 with
                   | (vars,guards,env',decls,uu____6070) ->
                       let fsym =
                         let uu____6088 = varops.fresh "f" in
                         (uu____6088, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____6091 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_6100 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_6100.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_6100.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_6100.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_6100.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_6100.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_6100.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_6100.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_6100.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_6100.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_6100.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_6100.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_6100.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_6100.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_6100.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_6100.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_6100.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_6100.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_6100.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_6100.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_6100.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_6100.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_6100.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_6100.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_6100.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_6100.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_6100.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____6091 with
                        | (pre_opt,res_t) ->
                            let uu____6111 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____6111 with
                             | (res_pred,decls') ->
                                 let uu____6122 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6135 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____6135, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6139 =
                                         encode_formula pre env' in
                                       (match uu____6139 with
                                        | (guard,decls0) ->
                                            let uu____6152 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____6152, decls0)) in
                                 (match uu____6122 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6164 =
                                          let uu____6175 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____6175) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6164 in
                                      let cvars =
                                        let uu____6193 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____6193
                                          (FStar_List.filter
                                             (fun uu____6207  ->
                                                match uu____6207 with
                                                | (x,uu____6213) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____6232 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____6232 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6240 =
                                             let uu____6241 =
                                               let uu____6248 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6248) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6241 in
                                           (uu____6240,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6268 =
                                               let uu____6269 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6269 in
                                             varops.mk_unique uu____6268 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____6280 =
                                               FStar_Options.log_queries () in
                                             if uu____6280
                                             then
                                               let uu____6283 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6283
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____6291 =
                                               let uu____6298 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____6298) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6291 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____6310 =
                                               let uu____6317 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____6317,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6310 in
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
                                             let uu____6338 =
                                               let uu____6345 =
                                                 let uu____6346 =
                                                   let uu____6357 =
                                                     let uu____6358 =
                                                       let uu____6363 =
                                                         let uu____6364 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6364 in
                                                       (f_has_t, uu____6363) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6358 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6357) in
                                                 mkForall_fuel uu____6346 in
                                               (uu____6345,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6338 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____6387 =
                                               let uu____6394 =
                                                 let uu____6395 =
                                                   let uu____6406 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6406) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6395 in
                                               (uu____6394,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6387 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____6431 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6431);
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
                     let uu____6446 =
                       let uu____6453 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____6453,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6446 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____6465 =
                       let uu____6472 =
                         let uu____6473 =
                           let uu____6484 =
                             let uu____6485 =
                               let uu____6490 =
                                 let uu____6491 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6491 in
                               (f_has_t, uu____6490) in
                             FStar_SMTEncoding_Util.mkImp uu____6485 in
                           ([[f_has_t]], [fsym], uu____6484) in
                         mkForall_fuel uu____6473 in
                       (uu____6472, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____6465 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6518 ->
           let uu____6527 =
             let uu____6532 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____6532 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____6539;
                 FStar_Syntax_Syntax.pos = uu____6540;
                 FStar_Syntax_Syntax.vars = uu____6541;_} ->
                 let uu____6554 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____6554 with
                  | (b,f1) ->
                      let uu____6579 =
                        let uu____6580 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____6580 in
                      (uu____6579, f1))
             | uu____6589 -> failwith "impossible" in
           (match uu____6527 with
            | (x,f) ->
                let uu____6600 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____6600 with
                 | (base_t,decls) ->
                     let uu____6611 = gen_term_var env x in
                     (match uu____6611 with
                      | (x1,xtm,env') ->
                          let uu____6625 = encode_formula f env' in
                          (match uu____6625 with
                           | (refinement,decls') ->
                               let uu____6636 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____6636 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____6652 =
                                        let uu____6655 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____6662 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____6655
                                          uu____6662 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6652 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6695  ->
                                              match uu____6695 with
                                              | (y,uu____6701) ->
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
                                    let uu____6734 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____6734 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6742 =
                                           let uu____6743 =
                                             let uu____6750 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6750) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6743 in
                                         (uu____6742,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____6771 =
                                             let uu____6772 =
                                               let uu____6773 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6773 in
                                             Prims.strcat module_name
                                               uu____6772 in
                                           varops.mk_unique uu____6771 in
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
                                           let uu____6787 =
                                             let uu____6794 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____6794) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6787 in
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
                                           let uu____6809 =
                                             let uu____6816 =
                                               let uu____6817 =
                                                 let uu____6828 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6828) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6817 in
                                             (uu____6816,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6809 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____6854 =
                                             let uu____6861 =
                                               let uu____6862 =
                                                 let uu____6873 =
                                                   let uu____6874 =
                                                     let uu____6879 =
                                                       let uu____6880 =
                                                         let uu____6891 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____6891) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____6880 in
                                                     (uu____6879, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____6874 in
                                                 ([[valid_t]], cvars1,
                                                   uu____6873) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6862 in
                                             (uu____6861,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6854 in
                                         let t_kinding =
                                           let uu____6929 =
                                             let uu____6936 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____6936,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6929 in
                                         let t_interp =
                                           let uu____6954 =
                                             let uu____6961 =
                                               let uu____6962 =
                                                 let uu____6973 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6973) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6962 in
                                             let uu____6996 =
                                               let uu____6999 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____6999 in
                                             (uu____6961, uu____6996,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6954 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____7006 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7006);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7044 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7044 in
           let uu____7045 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____7045 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7057 =
                    let uu____7064 =
                      let uu____7065 =
                        let uu____7066 =
                          let uu____7067 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7067 in
                        FStar_Util.format1 "uvar_typing_%s" uu____7066 in
                      varops.mk_unique uu____7065 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7064) in
                  FStar_SMTEncoding_Util.mkAssume uu____7057 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7072 ->
           let uu____7091 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____7091 with
            | (head1,args_e) ->
                let uu____7144 =
                  let uu____7159 =
                    let uu____7160 = FStar_Syntax_Subst.compress head1 in
                    uu____7160.FStar_Syntax_Syntax.n in
                  (uu____7159, args_e) in
                (match uu____7144 with
                 | uu____7179 when head_redex env head1 ->
                     let uu____7194 = whnf env t in
                     encode_term uu____7194 env
                 | uu____7195 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7218 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____7234;
                       FStar_Syntax_Syntax.pos = uu____7235;
                       FStar_Syntax_Syntax.vars = uu____7236;_},uu____7237),uu____7238::
                    (v1,uu____7240)::(v2,uu____7242)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7317 = encode_term v1 env in
                     (match uu____7317 with
                      | (v11,decls1) ->
                          let uu____7328 = encode_term v2 env in
                          (match uu____7328 with
                           | (v21,decls2) ->
                               let uu____7339 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7339,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7343::(v1,uu____7345)::(v2,uu____7347)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7414 = encode_term v1 env in
                     (match uu____7414 with
                      | (v11,decls1) ->
                          let uu____7425 = encode_term v2 env in
                          (match uu____7425 with
                           | (v21,decls2) ->
                               let uu____7436 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____7436,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7439) ->
                     let e0 =
                       let uu____7461 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7461 in
                     ((let uu____7471 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____7471
                       then
                         let uu____7472 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7472
                       else ());
                      (let e =
                         let uu____7479 =
                           let uu____7480 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____7481 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7480
                             uu____7481 in
                         uu____7479 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7492),(arg,uu____7494)::[]) -> encode_term arg env
                 | uu____7529 ->
                     let uu____7544 = encode_args args_e env in
                     (match uu____7544 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7603 = encode_term head1 env in
                            match uu____7603 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7675 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____7675 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7757  ->
                                                 fun uu____7758  ->
                                                   match (uu____7757,
                                                           uu____7758)
                                                   with
                                                   | ((bv,uu____7784),
                                                      (a,uu____7786)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____7812 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____7812
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____7821 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____7821 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____7836 =
                                                   let uu____7843 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____7852 =
                                                     let uu____7853 =
                                                       let uu____7854 =
                                                         let uu____7855 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____7855 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7854 in
                                                     varops.mk_unique
                                                       uu____7853 in
                                                   (uu____7843,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7852) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7836 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____7872 = lookup_free_var_sym env fv in
                            match uu____7872 with
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
                                   FStar_Syntax_Syntax.tk = uu____7907;
                                   FStar_Syntax_Syntax.pos = uu____7908;
                                   FStar_Syntax_Syntax.vars = uu____7909;_},uu____7910)
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
                                   FStar_Syntax_Syntax.tk = uu____7929;
                                   FStar_Syntax_Syntax.pos = uu____7930;
                                   FStar_Syntax_Syntax.vars = uu____7931;_},uu____7932)
                                ->
                                let uu____7941 =
                                  let uu____7942 =
                                    let uu____7947 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7947
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7942
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7941
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7977 =
                                  let uu____7978 =
                                    let uu____7983 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____7983
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____7978
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____7977
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8012,(FStar_Util.Inl t1,uu____8014),uu____8015)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8090,(FStar_Util.Inr c,uu____8092),uu____8093)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8168 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8205 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8205 in
                               let uu____8206 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____8206 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____8222;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8223;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8224;_},uu____8225)
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
                                     | uu____8243 ->
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
           let uu____8298 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____8298 with
            | (bs1,body1,opening) ->
                let fallback uu____8321 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____8328 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____8328, [decl]) in
                let is_impure rc =
                  let uu____8335 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____8335 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8347 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____8347
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8371 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____8371
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8375 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____8375)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8382 =
                         let uu____8383 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8383 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8382);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8385 =
                       (is_impure rc) &&
                         (let uu____8387 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____8387) in
                     if uu____8385
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____8394 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____8394 with
                        | (vars,guards,envbody,decls,uu____8419) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
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
                                       let uu____8474 = encode_term tfun env in
                                       (match uu____8474 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____8444 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8506 =
                                          let uu____8517 =
                                            let uu____8518 =
                                              let uu____8523 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____8523, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8518 in
                                          ([], vars, uu____8517) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8506 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8535 =
                                              let uu____8538 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____8538
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8535 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____8557 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____8557 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8565 =
                                             let uu____8566 =
                                               let uu____8573 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8573) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8566 in
                                           (uu____8565,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8584 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____8584 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8595 =
                                                    let uu____8596 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____8596 = cache_size in
                                                  if uu____8595
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
                                                    let uu____8612 =
                                                      let uu____8613 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8613 in
                                                    varops.mk_unique
                                                      uu____8612 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____8620 =
                                                    let uu____8627 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____8627) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8620 in
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
                                                      let uu____8645 =
                                                        let uu____8646 =
                                                          let uu____8653 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____8653,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8646 in
                                                      [uu____8645] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____8666 =
                                                    let uu____8673 =
                                                      let uu____8674 =
                                                        let uu____8685 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8685) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8674 in
                                                    (uu____8673,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8666 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____8702 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8702);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8705,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8706;
                          FStar_Syntax_Syntax.lbunivs = uu____8707;
                          FStar_Syntax_Syntax.lbtyp = uu____8708;
                          FStar_Syntax_Syntax.lbeff = uu____8709;
                          FStar_Syntax_Syntax.lbdef = uu____8710;_}::uu____8711),uu____8712)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8746;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8748;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8777 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____8799 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____8799, [decl_e])))
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
              let uu____8866 = encode_term e1 env in
              match uu____8866 with
              | (ee1,decls1) ->
                  let uu____8877 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____8877 with
                   | (xs,e21) ->
                       let uu____8902 = FStar_List.hd xs in
                       (match uu____8902 with
                        | (x1,uu____8916) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____8918 = encode_body e21 env' in
                            (match uu____8918 with
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
            let uu____8950 =
              let uu____8957 =
                let uu____8958 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____8958 in
              gen_term_var env uu____8957 in
            match uu____8950 with
            | (scrsym,scr',env1) ->
                let uu____8966 = encode_term e env1 in
                (match uu____8966 with
                 | (scr,decls) ->
                     let uu____8977 =
                       let encode_branch b uu____9002 =
                         match uu____9002 with
                         | (else_case,decls1) ->
                             let uu____9021 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____9021 with
                              | (p,w,br) ->
                                  let uu____9055 = encode_pat env1 p in
                                  (match uu____9055 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9092  ->
                                                   match uu____9092 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____9099 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9127 =
                                               encode_term w1 env2 in
                                             (match uu____9127 with
                                              | (w2,decls2) ->
                                                  let uu____9140 =
                                                    let uu____9141 =
                                                      let uu____9146 =
                                                        let uu____9147 =
                                                          let uu____9152 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____9152) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9147 in
                                                      (guard, uu____9146) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9141 in
                                                  (uu____9140, decls2)) in
                                       (match uu____9099 with
                                        | (guard1,decls2) ->
                                            let uu____9165 =
                                              encode_br br env2 in
                                            (match uu____9165 with
                                             | (br1,decls3) ->
                                                 let uu____9178 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____9178,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____8977 with
                      | (match_tm,decls1) ->
                          let uu____9197 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____9197, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9237 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____9237
       then
         let uu____9238 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9238
       else ());
      (let uu____9240 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____9240 with
       | (vars,pat_term) ->
           let uu____9257 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9310  ->
                     fun v1  ->
                       match uu____9310 with
                       | (env1,vars1) ->
                           let uu____9362 = gen_term_var env1 v1 in
                           (match uu____9362 with
                            | (xx,uu____9384,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____9257 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9463 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9464 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9465 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9475 =
                        let uu____9480 = encode_const c in
                        (scrutinee, uu____9480) in
                      FStar_SMTEncoding_Util.mkEq uu____9475
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____9501 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____9501 with
                        | (uu____9508,uu____9509::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9512 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9545  ->
                                  match uu____9545 with
                                  | (arg,uu____9553) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9559 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____9559)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9586) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9621 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9644 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9688  ->
                                  match uu____9688 with
                                  | (arg,uu____9702) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____9708 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____9708)) in
                      FStar_All.pipe_right uu____9644 FStar_List.flatten in
                let pat_term1 uu____9736 = encode_term pat_term env1 in
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
      let uu____9746 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9784  ->
                fun uu____9785  ->
                  match (uu____9784, uu____9785) with
                  | ((tms,decls),(t,uu____9821)) ->
                      let uu____9842 = encode_term t env in
                      (match uu____9842 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____9746 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9899 = FStar_Syntax_Util.list_elements e in
        match uu____9899 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____9922 =
          let uu____9941 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____9941 FStar_Syntax_Util.head_and_args in
        match uu____9922 with
        | (head1,args) ->
            let uu____9994 =
              let uu____10009 =
                let uu____10010 = FStar_Syntax_Util.un_uinst head1 in
                uu____10010.FStar_Syntax_Syntax.n in
              (uu____10009, args) in
            (match uu____9994 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10030,uu____10031)::(e,uu____10033)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10084 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____10128 =
            let uu____10147 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____10147 FStar_Syntax_Util.head_and_args in
          match uu____10128 with
          | (head1,args) ->
              let uu____10202 =
                let uu____10217 =
                  let uu____10218 = FStar_Syntax_Util.un_uinst head1 in
                  uu____10218.FStar_Syntax_Syntax.n in
                (uu____10217, args) in
              (match uu____10202 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10241)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10280 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____10308 = smt_pat_or1 t1 in
            (match uu____10308 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10332 = list_elements1 e in
                 FStar_All.pipe_right uu____10332
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10354 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____10354
                           (FStar_List.map one_pat)))
             | uu____10369 ->
                 let uu____10376 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____10376])
        | uu____10407 ->
            let uu____10410 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____10410] in
      let uu____10441 =
        let uu____10466 =
          let uu____10467 = FStar_Syntax_Subst.compress t in
          uu____10467.FStar_Syntax_Syntax.n in
        match uu____10466 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10518 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____10518 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10573;
                        FStar_Syntax_Syntax.effect_name = uu____10574;
                        FStar_Syntax_Syntax.result_typ = uu____10575;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10577)::(post,uu____10579)::(pats,uu____10581)::[];
                        FStar_Syntax_Syntax.flags = uu____10582;_}
                      ->
                      let uu____10645 = lemma_pats pats in
                      (binders1, pre, post, uu____10645)
                  | uu____10670 -> failwith "impos"))
        | uu____10695 -> failwith "Impos" in
      match uu____10441 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_10761 = env in
            {
              bindings = (uu___136_10761.bindings);
              depth = (uu___136_10761.depth);
              tcenv = (uu___136_10761.tcenv);
              warn = (uu___136_10761.warn);
              cache = (uu___136_10761.cache);
              nolabels = (uu___136_10761.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_10761.encode_non_total_function_typ);
              current_module_name = (uu___136_10761.current_module_name)
            } in
          let uu____10762 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____10762 with
           | (vars,guards,env2,decls,uu____10787) ->
               let uu____10800 =
                 let uu____10813 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10859 =
                             let uu____10868 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____10868
                               FStar_List.unzip in
                           match uu____10859 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____10813 FStar_List.unzip in
               (match uu____10800 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_10977 = env2 in
                      {
                        bindings = (uu___137_10977.bindings);
                        depth = (uu___137_10977.depth);
                        tcenv = (uu___137_10977.tcenv);
                        warn = (uu___137_10977.warn);
                        cache = (uu___137_10977.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_10977.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_10977.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_10977.current_module_name)
                      } in
                    let uu____10978 =
                      let uu____10983 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____10983 env3 in
                    (match uu____10978 with
                     | (pre1,decls'') ->
                         let uu____10990 =
                           let uu____10995 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____10995 env3 in
                         (match uu____10990 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____11005 =
                                let uu____11006 =
                                  let uu____11017 =
                                    let uu____11018 =
                                      let uu____11023 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____11023, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____11018 in
                                  (pats, vars, uu____11017) in
                                FStar_SMTEncoding_Util.mkForall uu____11006 in
                              (uu____11005, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____11042 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____11042
        then
          let uu____11043 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____11044 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____11043 uu____11044
        else () in
      let enc f r l =
        let uu____11077 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11105 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____11105 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____11077 with
        | (decls,args) ->
            let uu____11134 =
              let uu___138_11135 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_11135.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_11135.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11134, decls) in
      let const_op f r uu____11168 =
        let uu____11183 = f r in (uu____11183, []) in
      let un_op f l =
        let uu____11202 = FStar_List.hd l in
        FStar_All.pipe_left f uu____11202 in
      let bin_op f uu___112_11218 =
        match uu___112_11218 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11229 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____11263 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11286  ->
                 match uu____11286 with
                 | (t,uu____11300) ->
                     let uu____11301 = encode_formula t env in
                     (match uu____11301 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____11263 with
        | (decls,phis) ->
            let uu____11330 =
              let uu___139_11331 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_11331.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_11331.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____11330, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11400  ->
               match uu____11400 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11425) -> false
                    | uu____11426 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11443 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____11443
        else
          (let uu____11459 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____11459 r rf) in
      let mk_imp1 r uu___113_11484 =
        match uu___113_11484 with
        | (lhs,uu____11490)::(rhs,uu____11492)::[] ->
            let uu____11533 = encode_formula rhs env in
            (match uu____11533 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11548) ->
                      (l1, decls1)
                  | uu____11553 ->
                      let uu____11554 = encode_formula lhs env in
                      (match uu____11554 with
                       | (l2,decls2) ->
                           let uu____11565 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____11565, (FStar_List.append decls1 decls2)))))
        | uu____11568 -> failwith "impossible" in
      let mk_ite r uu___114_11589 =
        match uu___114_11589 with
        | (guard,uu____11595)::(_then,uu____11597)::(_else,uu____11599)::[]
            ->
            let uu____11656 = encode_formula guard env in
            (match uu____11656 with
             | (g,decls1) ->
                 let uu____11667 = encode_formula _then env in
                 (match uu____11667 with
                  | (t,decls2) ->
                      let uu____11678 = encode_formula _else env in
                      (match uu____11678 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11692 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____11717 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____11717 in
      let connectives =
        let uu____11735 =
          let uu____11748 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____11748) in
        let uu____11765 =
          let uu____11780 =
            let uu____11793 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____11793) in
          let uu____11810 =
            let uu____11825 =
              let uu____11840 =
                let uu____11853 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____11853) in
              let uu____11870 =
                let uu____11885 =
                  let uu____11900 =
                    let uu____11913 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____11913) in
                  [uu____11900;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11885 in
              uu____11840 :: uu____11870 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11825 in
          uu____11780 :: uu____11810 in
        uu____11735 :: uu____11765 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12260 = encode_formula phi' env in
            (match uu____12260 with
             | (phi2,decls) ->
                 let uu____12271 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____12271, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12272 ->
            let uu____12281 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____12281 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12332 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____12332 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12344;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12346;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12375 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____12375 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12432::(x,uu____12434)::(t,uu____12436)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12503 = encode_term x env in
                 (match uu____12503 with
                  | (x1,decls) ->
                      let uu____12514 = encode_term t env in
                      (match uu____12514 with
                       | (t1,decls') ->
                           let uu____12525 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____12525, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12530)::(msg,uu____12532)::(phi2,uu____12534)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12601 =
                   let uu____12606 =
                     let uu____12607 = FStar_Syntax_Subst.compress r in
                     uu____12607.FStar_Syntax_Syntax.n in
                   let uu____12612 =
                     let uu____12613 = FStar_Syntax_Subst.compress msg in
                     uu____12613.FStar_Syntax_Syntax.n in
                   (uu____12606, uu____12612) in
                 (match uu____12601 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12624))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____12638 -> fallback phi2)
             | uu____12643 when head_redex env head2 ->
                 let uu____12658 = whnf env phi1 in
                 encode_formula uu____12658 env
             | uu____12659 ->
                 let uu____12674 = encode_term phi1 env in
                 (match uu____12674 with
                  | (tt,decls) ->
                      let uu____12685 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_12688 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_12688.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_12688.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____12685, decls)))
        | uu____12689 ->
            let uu____12690 = encode_term phi1 env in
            (match uu____12690 with
             | (tt,decls) ->
                 let uu____12701 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_12704 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_12704.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_12704.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____12701, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____12740 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____12740 with
        | (vars,guards,env2,decls,uu____12779) ->
            let uu____12792 =
              let uu____12805 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12853 =
                          let uu____12862 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12892  ->
                                    match uu____12892 with
                                    | (t,uu____12902) ->
                                        encode_term t
                                          (let uu___142_12904 = env2 in
                                           {
                                             bindings =
                                               (uu___142_12904.bindings);
                                             depth = (uu___142_12904.depth);
                                             tcenv = (uu___142_12904.tcenv);
                                             warn = (uu___142_12904.warn);
                                             cache = (uu___142_12904.cache);
                                             nolabels =
                                               (uu___142_12904.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_12904.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_12904.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____12862 FStar_List.unzip in
                        match uu____12853 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____12805 FStar_List.unzip in
            (match uu____12792 with
             | (pats,decls') ->
                 let uu____13003 = encode_formula body env2 in
                 (match uu____13003 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____13035;
                             FStar_SMTEncoding_Term.rng = uu____13036;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____13051 -> guards in
                      let uu____13056 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____13056, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____13116  ->
                   match uu____13116 with
                   | (x,uu____13122) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____13130 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____13142 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____13142) uu____13130 tl1 in
             let uu____13145 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____13172  ->
                       match uu____13172 with
                       | (b,uu____13178) ->
                           let uu____13179 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____13179)) in
             (match uu____13145 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____13185) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____13203 =
                    let uu____13204 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____13204 in
                  FStar_Errors.warn pos uu____13203) in
       let uu____13205 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____13205 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____13214 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13272  ->
                     match uu____13272 with
                     | (l,uu____13286) -> FStar_Ident.lid_equals op l)) in
           (match uu____13214 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13319,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13359 = encode_q_body env vars pats body in
             match uu____13359 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13404 =
                     let uu____13415 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____13415) in
                   FStar_SMTEncoding_Term.mkForall uu____13404
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13434 = encode_q_body env vars pats body in
             match uu____13434 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13478 =
                   let uu____13479 =
                     let uu____13490 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____13490) in
                   FStar_SMTEncoding_Term.mkExists uu____13479
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____13478, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}
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
  let uu____13588 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____13588 with
  | (asym,a) ->
      let uu____13595 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____13595 with
       | (xsym,x) ->
           let uu____13602 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____13602 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13646 =
                      let uu____13657 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____13657, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13646 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____13683 =
                      let uu____13690 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____13690) in
                    FStar_SMTEncoding_Util.mkApp uu____13683 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____13703 =
                    let uu____13706 =
                      let uu____13709 =
                        let uu____13712 =
                          let uu____13713 =
                            let uu____13720 =
                              let uu____13721 =
                                let uu____13732 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____13732) in
                              FStar_SMTEncoding_Util.mkForall uu____13721 in
                            (uu____13720, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____13713 in
                        let uu____13749 =
                          let uu____13752 =
                            let uu____13753 =
                              let uu____13760 =
                                let uu____13761 =
                                  let uu____13772 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____13772) in
                                FStar_SMTEncoding_Util.mkForall uu____13761 in
                              (uu____13760,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____13753 in
                          [uu____13752] in
                        uu____13712 :: uu____13749 in
                      xtok_decl :: uu____13709 in
                    xname_decl :: uu____13706 in
                  (xtok1, uu____13703) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____13863 =
                    let uu____13876 =
                      let uu____13885 =
                        let uu____13886 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13886 in
                      quant axy uu____13885 in
                    (FStar_Parser_Const.op_Eq, uu____13876) in
                  let uu____13895 =
                    let uu____13910 =
                      let uu____13923 =
                        let uu____13932 =
                          let uu____13933 =
                            let uu____13934 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____13934 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13933 in
                        quant axy uu____13932 in
                      (FStar_Parser_Const.op_notEq, uu____13923) in
                    let uu____13943 =
                      let uu____13958 =
                        let uu____13971 =
                          let uu____13980 =
                            let uu____13981 =
                              let uu____13982 =
                                let uu____13987 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____13988 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____13987, uu____13988) in
                              FStar_SMTEncoding_Util.mkLT uu____13982 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13981 in
                          quant xy uu____13980 in
                        (FStar_Parser_Const.op_LT, uu____13971) in
                      let uu____13997 =
                        let uu____14012 =
                          let uu____14025 =
                            let uu____14034 =
                              let uu____14035 =
                                let uu____14036 =
                                  let uu____14041 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____14042 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____14041, uu____14042) in
                                FStar_SMTEncoding_Util.mkLTE uu____14036 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____14035 in
                            quant xy uu____14034 in
                          (FStar_Parser_Const.op_LTE, uu____14025) in
                        let uu____14051 =
                          let uu____14066 =
                            let uu____14079 =
                              let uu____14088 =
                                let uu____14089 =
                                  let uu____14090 =
                                    let uu____14095 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____14096 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____14095, uu____14096) in
                                  FStar_SMTEncoding_Util.mkGT uu____14090 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____14089 in
                              quant xy uu____14088 in
                            (FStar_Parser_Const.op_GT, uu____14079) in
                          let uu____14105 =
                            let uu____14120 =
                              let uu____14133 =
                                let uu____14142 =
                                  let uu____14143 =
                                    let uu____14144 =
                                      let uu____14149 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____14150 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____14149, uu____14150) in
                                    FStar_SMTEncoding_Util.mkGTE uu____14144 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____14143 in
                                quant xy uu____14142 in
                              (FStar_Parser_Const.op_GTE, uu____14133) in
                            let uu____14159 =
                              let uu____14174 =
                                let uu____14187 =
                                  let uu____14196 =
                                    let uu____14197 =
                                      let uu____14198 =
                                        let uu____14203 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____14204 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____14203, uu____14204) in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____14198 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____14197 in
                                  quant xy uu____14196 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____14187) in
                              let uu____14213 =
                                let uu____14228 =
                                  let uu____14241 =
                                    let uu____14250 =
                                      let uu____14251 =
                                        let uu____14252 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14252 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14251 in
                                    quant qx uu____14250 in
                                  (FStar_Parser_Const.op_Minus, uu____14241) in
                                let uu____14261 =
                                  let uu____14276 =
                                    let uu____14289 =
                                      let uu____14298 =
                                        let uu____14299 =
                                          let uu____14300 =
                                            let uu____14305 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____14306 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____14305, uu____14306) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14300 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14299 in
                                      quant xy uu____14298 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14289) in
                                  let uu____14315 =
                                    let uu____14330 =
                                      let uu____14343 =
                                        let uu____14352 =
                                          let uu____14353 =
                                            let uu____14354 =
                                              let uu____14359 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____14360 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____14359, uu____14360) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14354 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14353 in
                                        quant xy uu____14352 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14343) in
                                    let uu____14369 =
                                      let uu____14384 =
                                        let uu____14397 =
                                          let uu____14406 =
                                            let uu____14407 =
                                              let uu____14408 =
                                                let uu____14413 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____14414 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____14413, uu____14414) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14408 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14407 in
                                          quant xy uu____14406 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14397) in
                                      let uu____14423 =
                                        let uu____14438 =
                                          let uu____14451 =
                                            let uu____14460 =
                                              let uu____14461 =
                                                let uu____14462 =
                                                  let uu____14467 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____14468 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____14467, uu____14468) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14462 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14461 in
                                            quant xy uu____14460 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14451) in
                                        let uu____14477 =
                                          let uu____14492 =
                                            let uu____14505 =
                                              let uu____14514 =
                                                let uu____14515 =
                                                  let uu____14516 =
                                                    let uu____14521 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____14522 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____14521,
                                                      uu____14522) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14516 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14515 in
                                              quant xy uu____14514 in
                                            (FStar_Parser_Const.op_And,
                                              uu____14505) in
                                          let uu____14531 =
                                            let uu____14546 =
                                              let uu____14559 =
                                                let uu____14568 =
                                                  let uu____14569 =
                                                    let uu____14570 =
                                                      let uu____14575 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____14576 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____14575,
                                                        uu____14576) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14570 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14569 in
                                                quant xy uu____14568 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14559) in
                                            let uu____14585 =
                                              let uu____14600 =
                                                let uu____14613 =
                                                  let uu____14622 =
                                                    let uu____14623 =
                                                      let uu____14624 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14624 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14623 in
                                                  quant qx uu____14622 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14613) in
                                              [uu____14600] in
                                            uu____14546 :: uu____14585 in
                                          uu____14492 :: uu____14531 in
                                        uu____14438 :: uu____14477 in
                                      uu____14384 :: uu____14423 in
                                    uu____14330 :: uu____14369 in
                                  uu____14276 :: uu____14315 in
                                uu____14228 :: uu____14261 in
                              uu____14174 :: uu____14213 in
                            uu____14120 :: uu____14159 in
                          uu____14066 :: uu____14105 in
                        uu____14012 :: uu____14051 in
                      uu____13958 :: uu____13997 in
                    uu____13910 :: uu____13943 in
                  uu____13863 :: uu____13895 in
                let mk1 l v1 =
                  let uu____14838 =
                    let uu____14847 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14905  ->
                              match uu____14905 with
                              | (l',uu____14919) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____14847
                      (FStar_Option.map
                         (fun uu____14979  ->
                            match uu____14979 with | (uu____14998,b) -> b v1)) in
                  FStar_All.pipe_right uu____14838 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____15069  ->
                          match uu____15069 with
                          | (l',uu____15083) -> FStar_Ident.lid_equals l l')) in
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
        let uu____15124 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____15124 with
        | (xxsym,xx) ->
            let uu____15131 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____15131 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____15141 =
                   let uu____15148 =
                     let uu____15149 =
                       let uu____15160 =
                         let uu____15161 =
                           let uu____15166 =
                             let uu____15167 =
                               let uu____15172 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____15172) in
                             FStar_SMTEncoding_Util.mkEq uu____15167 in
                           (xx_has_type, uu____15166) in
                         FStar_SMTEncoding_Util.mkImp uu____15161 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____15160) in
                     FStar_SMTEncoding_Util.mkForall uu____15149 in
                   let uu____15197 =
                     let uu____15198 =
                       let uu____15199 =
                         let uu____15200 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____15200 in
                       Prims.strcat module_name uu____15199 in
                     varops.mk_unique uu____15198 in
                   (uu____15148, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____15197) in
                 FStar_SMTEncoding_Util.mkAssume uu____15141)
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
    let uu____15240 =
      let uu____15241 =
        let uu____15248 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____15248, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15241 in
    let uu____15251 =
      let uu____15254 =
        let uu____15255 =
          let uu____15262 =
            let uu____15263 =
              let uu____15274 =
                let uu____15275 =
                  let uu____15280 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____15280) in
                FStar_SMTEncoding_Util.mkImp uu____15275 in
              ([[typing_pred]], [xx], uu____15274) in
            mkForall_fuel uu____15263 in
          (uu____15262, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15255 in
      [uu____15254] in
    uu____15240 :: uu____15251 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15322 =
      let uu____15323 =
        let uu____15330 =
          let uu____15331 =
            let uu____15342 =
              let uu____15347 =
                let uu____15350 = FStar_SMTEncoding_Term.boxBool b in
                [uu____15350] in
              [uu____15347] in
            let uu____15355 =
              let uu____15356 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____15356 tt in
            (uu____15342, [bb], uu____15355) in
          FStar_SMTEncoding_Util.mkForall uu____15331 in
        (uu____15330, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15323 in
    let uu____15377 =
      let uu____15380 =
        let uu____15381 =
          let uu____15388 =
            let uu____15389 =
              let uu____15400 =
                let uu____15401 =
                  let uu____15406 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x in
                  (typing_pred, uu____15406) in
                FStar_SMTEncoding_Util.mkImp uu____15401 in
              ([[typing_pred]], [xx], uu____15400) in
            mkForall_fuel uu____15389 in
          (uu____15388, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15381 in
      [uu____15380] in
    uu____15322 :: uu____15377 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____15456 =
        let uu____15457 =
          let uu____15464 =
            let uu____15467 =
              let uu____15470 =
                let uu____15473 = FStar_SMTEncoding_Term.boxInt a in
                let uu____15474 =
                  let uu____15477 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____15477] in
                uu____15473 :: uu____15474 in
              tt :: uu____15470 in
            tt :: uu____15467 in
          ("Prims.Precedes", uu____15464) in
        FStar_SMTEncoding_Util.mkApp uu____15457 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15456 in
    let precedes_y_x =
      let uu____15481 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15481 in
    let uu____15484 =
      let uu____15485 =
        let uu____15492 =
          let uu____15493 =
            let uu____15504 =
              let uu____15509 =
                let uu____15512 = FStar_SMTEncoding_Term.boxInt b in
                [uu____15512] in
              [uu____15509] in
            let uu____15517 =
              let uu____15518 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____15518 tt in
            (uu____15504, [bb], uu____15517) in
          FStar_SMTEncoding_Util.mkForall uu____15493 in
        (uu____15492, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15485 in
    let uu____15539 =
      let uu____15542 =
        let uu____15543 =
          let uu____15550 =
            let uu____15551 =
              let uu____15562 =
                let uu____15563 =
                  let uu____15568 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x in
                  (typing_pred, uu____15568) in
                FStar_SMTEncoding_Util.mkImp uu____15563 in
              ([[typing_pred]], [xx], uu____15562) in
            mkForall_fuel uu____15551 in
          (uu____15550, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15543 in
      let uu____15593 =
        let uu____15596 =
          let uu____15597 =
            let uu____15604 =
              let uu____15605 =
                let uu____15616 =
                  let uu____15617 =
                    let uu____15622 =
                      let uu____15623 =
                        let uu____15626 =
                          let uu____15629 =
                            let uu____15632 =
                              let uu____15633 =
                                let uu____15638 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____15639 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____15638, uu____15639) in
                              FStar_SMTEncoding_Util.mkGT uu____15633 in
                            let uu____15640 =
                              let uu____15643 =
                                let uu____15644 =
                                  let uu____15649 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____15650 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____15649, uu____15650) in
                                FStar_SMTEncoding_Util.mkGTE uu____15644 in
                              let uu____15651 =
                                let uu____15654 =
                                  let uu____15655 =
                                    let uu____15660 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____15661 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____15660, uu____15661) in
                                  FStar_SMTEncoding_Util.mkLT uu____15655 in
                                [uu____15654] in
                              uu____15643 :: uu____15651 in
                            uu____15632 :: uu____15640 in
                          typing_pred_y :: uu____15629 in
                        typing_pred :: uu____15626 in
                      FStar_SMTEncoding_Util.mk_and_l uu____15623 in
                    (uu____15622, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____15617 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15616) in
              mkForall_fuel uu____15605 in
            (uu____15604,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____15597 in
        [uu____15596] in
      uu____15542 :: uu____15593 in
    uu____15484 :: uu____15539 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____15707 =
      let uu____15708 =
        let uu____15715 =
          let uu____15716 =
            let uu____15727 =
              let uu____15732 =
                let uu____15735 = FStar_SMTEncoding_Term.boxString b in
                [uu____15735] in
              [uu____15732] in
            let uu____15740 =
              let uu____15741 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____15741 tt in
            (uu____15727, [bb], uu____15740) in
          FStar_SMTEncoding_Util.mkForall uu____15716 in
        (uu____15715, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____15708 in
    let uu____15762 =
      let uu____15765 =
        let uu____15766 =
          let uu____15773 =
            let uu____15774 =
              let uu____15785 =
                let uu____15786 =
                  let uu____15791 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x in
                  (typing_pred, uu____15791) in
                FStar_SMTEncoding_Util.mkImp uu____15786 in
              ([[typing_pred]], [xx], uu____15785) in
            mkForall_fuel uu____15774 in
          (uu____15773, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____15766 in
      [uu____15765] in
    uu____15707 :: uu____15762 in
  let mk_ref1 env reft_name uu____15825 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____15842 =
        let uu____15849 =
          let uu____15852 = FStar_SMTEncoding_Util.mkFreeV aa in
          [uu____15852] in
        (reft_name, uu____15849) in
      FStar_SMTEncoding_Util.mkApp uu____15842 in
    let refb =
      let uu____15856 =
        let uu____15863 =
          let uu____15866 = FStar_SMTEncoding_Util.mkFreeV bb in
          [uu____15866] in
        (reft_name, uu____15863) in
      FStar_SMTEncoding_Util.mkApp uu____15856 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____15871 =
      let uu____15872 =
        let uu____15879 =
          let uu____15880 =
            let uu____15891 =
              let uu____15892 =
                let uu____15897 =
                  FStar_SMTEncoding_Term.mk_tester
                    (FStar_Pervasives_Native.fst
                       FStar_SMTEncoding_Term.boxRefFun) x in
                (typing_pred, uu____15897) in
              FStar_SMTEncoding_Util.mkImp uu____15892 in
            ([[typing_pred]], [xx; aa], uu____15891) in
          mkForall_fuel uu____15880 in
        (uu____15879, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____15872 in
    [uu____15871] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____15954 =
      let uu____15955 =
        let uu____15962 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____15962, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____15955 in
    [uu____15954] in
  let mk_and_interp env conj uu____15974 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____15999 =
      let uu____16000 =
        let uu____16007 =
          let uu____16008 =
            let uu____16019 =
              let uu____16020 =
                let uu____16025 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____16025, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16020 in
            ([[l_and_a_b]], [aa; bb], uu____16019) in
          FStar_SMTEncoding_Util.mkForall uu____16008 in
        (uu____16007, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16000 in
    [uu____15999] in
  let mk_or_interp env disj uu____16063 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16088 =
      let uu____16089 =
        let uu____16096 =
          let uu____16097 =
            let uu____16108 =
              let uu____16109 =
                let uu____16114 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____16114, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16109 in
            ([[l_or_a_b]], [aa; bb], uu____16108) in
          FStar_SMTEncoding_Util.mkForall uu____16097 in
        (uu____16096, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16089 in
    [uu____16088] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____16177 =
      let uu____16178 =
        let uu____16185 =
          let uu____16186 =
            let uu____16197 =
              let uu____16198 =
                let uu____16203 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____16203, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16198 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____16197) in
          FStar_SMTEncoding_Util.mkForall uu____16186 in
        (uu____16185, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16178 in
    [uu____16177] in
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
    let uu____16276 =
      let uu____16277 =
        let uu____16284 =
          let uu____16285 =
            let uu____16296 =
              let uu____16297 =
                let uu____16302 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____16302, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16297 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____16296) in
          FStar_SMTEncoding_Util.mkForall uu____16285 in
        (uu____16284, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16277 in
    [uu____16276] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16373 =
      let uu____16374 =
        let uu____16381 =
          let uu____16382 =
            let uu____16393 =
              let uu____16394 =
                let uu____16399 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____16399, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16394 in
            ([[l_imp_a_b]], [aa; bb], uu____16393) in
          FStar_SMTEncoding_Util.mkForall uu____16382 in
        (uu____16381, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16374 in
    [uu____16373] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____16462 =
      let uu____16463 =
        let uu____16470 =
          let uu____16471 =
            let uu____16482 =
              let uu____16483 =
                let uu____16488 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____16488, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16483 in
            ([[l_iff_a_b]], [aa; bb], uu____16482) in
          FStar_SMTEncoding_Util.mkForall uu____16471 in
        (uu____16470, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16463 in
    [uu____16462] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____16540 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16540 in
    let uu____16543 =
      let uu____16544 =
        let uu____16551 =
          let uu____16552 =
            let uu____16563 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____16563) in
          FStar_SMTEncoding_Util.mkForall uu____16552 in
        (uu____16551, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16544 in
    [uu____16543] in
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
      let uu____16623 =
        let uu____16630 =
          let uu____16633 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16633] in
        ("Valid", uu____16630) in
      FStar_SMTEncoding_Util.mkApp uu____16623 in
    let uu____16636 =
      let uu____16637 =
        let uu____16644 =
          let uu____16645 =
            let uu____16656 =
              let uu____16657 =
                let uu____16662 =
                  let uu____16663 =
                    let uu____16674 =
                      let uu____16679 =
                        let uu____16682 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16682] in
                      [uu____16679] in
                    let uu____16687 =
                      let uu____16688 =
                        let uu____16693 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16693, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16688 in
                    (uu____16674, [xx1], uu____16687) in
                  FStar_SMTEncoding_Util.mkForall uu____16663 in
                (uu____16662, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16657 in
            ([[l_forall_a_b]], [aa; bb], uu____16656) in
          FStar_SMTEncoding_Util.mkForall uu____16645 in
        (uu____16644, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16637 in
    [uu____16636] in
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
      let uu____16775 =
        let uu____16782 =
          let uu____16785 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____16785] in
        ("Valid", uu____16782) in
      FStar_SMTEncoding_Util.mkApp uu____16775 in
    let uu____16788 =
      let uu____16789 =
        let uu____16796 =
          let uu____16797 =
            let uu____16808 =
              let uu____16809 =
                let uu____16814 =
                  let uu____16815 =
                    let uu____16826 =
                      let uu____16831 =
                        let uu____16834 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____16834] in
                      [uu____16831] in
                    let uu____16839 =
                      let uu____16840 =
                        let uu____16845 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____16845, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____16840 in
                    (uu____16826, [xx1], uu____16839) in
                  FStar_SMTEncoding_Util.mkExists uu____16815 in
                (uu____16814, valid) in
              FStar_SMTEncoding_Util.mkIff uu____16809 in
            ([[l_exists_a_b]], [aa; bb], uu____16808) in
          FStar_SMTEncoding_Util.mkForall uu____16797 in
        (uu____16796, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____16789 in
    [uu____16788] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____16905 =
      let uu____16906 =
        let uu____16913 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____16914 = varops.mk_unique "typing_range_const" in
        (uu____16913, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16914) in
      FStar_SMTEncoding_Util.mkAssume uu____16906 in
    [uu____16905] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.ref_lid, mk_ref1);
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
    (FStar_Parser_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____17216 =
            FStar_Util.find_opt
              (fun uu____17242  ->
                 match uu____17242 with
                 | (l,uu____17254) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____17216 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17279,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____17318 = encode_function_type_as_formula t env in
        match uu____17318 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____17360 =
              (let uu____17363 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____17363) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____17360
            then
              let uu____17370 = new_term_constant_and_tok_from_lid env lid in
              match uu____17370 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____17389 =
                      let uu____17390 = FStar_Syntax_Subst.compress t_norm in
                      uu____17390.FStar_Syntax_Syntax.n in
                    match uu____17389 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17398) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____17432  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____17437 -> [] in
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
              (let uu____17451 = prims.is lid in
               if uu____17451
               then
                 let vname = varops.new_fvar lid in
                 let uu____17459 = prims.mk lid vname in
                 match uu____17459 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____17483 =
                    let uu____17494 = curried_arrow_formals_comp t_norm in
                    match uu____17494 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____17512 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____17512
                          then
                            let uu____17513 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_17516 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_17516.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_17516.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_17516.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_17516.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_17516.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_17516.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_17516.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_17516.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_17516.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_17516.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_17516.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_17516.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_17516.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_17516.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_17516.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_17516.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_17516.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_17516.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_17516.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_17516.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_17516.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_17516.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_17516.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_17516.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_17516.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_17516.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____17513
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____17528 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____17528)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____17483 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____17577 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____17577 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____17598 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_17640  ->
                                     match uu___115_17640 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____17644 =
                                           FStar_Util.prefix vars in
                                         (match uu____17644 with
                                          | (uu____17665,(xxsym,uu____17667))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____17685 =
                                                let uu____17686 =
                                                  let uu____17693 =
                                                    let uu____17694 =
                                                      let uu____17705 =
                                                        let uu____17706 =
                                                          let uu____17711 =
                                                            let uu____17712 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____17712 in
                                                          (vapp, uu____17711) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____17706 in
                                                      ([[vapp]], vars,
                                                        uu____17705) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____17694 in
                                                  (uu____17693,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____17686 in
                                              [uu____17685])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____17731 =
                                           FStar_Util.prefix vars in
                                         (match uu____17731 with
                                          | (uu____17752,(xxsym,uu____17754))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____17777 =
                                                let uu____17778 =
                                                  let uu____17785 =
                                                    let uu____17786 =
                                                      let uu____17797 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____17797) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____17786 in
                                                  (uu____17785,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____17778 in
                                              [uu____17777])
                                     | uu____17814 -> [])) in
                           let uu____17815 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____17815 with
                            | (vars,guards,env',decls1,uu____17842) ->
                                let uu____17855 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____17864 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____17864, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____17866 = encode_formula p env' in
                                      (match uu____17866 with
                                       | (g,ds) ->
                                           let uu____17877 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____17877,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____17855 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____17890 =
                                         let uu____17897 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____17897) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____17890 in
                                     let uu____17906 =
                                       let vname_decl =
                                         let uu____17914 =
                                           let uu____17925 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____17935  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____17925,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____17914 in
                                       let uu____17944 =
                                         let env2 =
                                           let uu___144_17950 = env1 in
                                           {
                                             bindings =
                                               (uu___144_17950.bindings);
                                             depth = (uu___144_17950.depth);
                                             tcenv = (uu___144_17950.tcenv);
                                             warn = (uu___144_17950.warn);
                                             cache = (uu___144_17950.cache);
                                             nolabels =
                                               (uu___144_17950.nolabels);
                                             use_zfuel_name =
                                               (uu___144_17950.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_17950.current_module_name)
                                           } in
                                         let uu____17951 =
                                           let uu____17952 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____17952 in
                                         if uu____17951
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____17944 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____17967::uu____17968 ->
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
                                                   let uu____18008 =
                                                     let uu____18019 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____18019) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____18008 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____18046 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____18049 =
                                             match formals with
                                             | [] ->
                                                 let uu____18066 =
                                                   let uu____18067 =
                                                     let uu____18070 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____18070 in
                                                   push_free_var env1 lid
                                                     vname uu____18067 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____18066)
                                             | uu____18075 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____18082 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____18082 in
                                                 let name_tok_corr =
                                                   let uu____18084 =
                                                     let uu____18091 =
                                                       let uu____18092 =
                                                         let uu____18103 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____18103) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____18092 in
                                                     (uu____18091,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____18084 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____18049 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____17906 with
                                      | (decls2,env2) ->
                                          let uu____18146 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____18154 =
                                              encode_term res_t1 env' in
                                            match uu____18154 with
                                            | (encoded_res_t,decls) ->
                                                let uu____18167 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____18167,
                                                  decls) in
                                          (match uu____18146 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____18178 =
                                                   let uu____18185 =
                                                     let uu____18186 =
                                                       let uu____18197 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____18197) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____18186 in
                                                   (uu____18185,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____18178 in
                                               let freshness =
                                                 let uu____18213 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____18213
                                                 then
                                                   let uu____18218 =
                                                     let uu____18219 =
                                                       let uu____18230 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____18241 =
                                                         varops.next_id () in
                                                       (vname, uu____18230,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____18241) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____18219 in
                                                   let uu____18244 =
                                                     let uu____18247 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____18247] in
                                                   uu____18218 :: uu____18244
                                                 else [] in
                                               let g =
                                                 let uu____18252 =
                                                   let uu____18255 =
                                                     let uu____18258 =
                                                       let uu____18261 =
                                                         let uu____18264 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____18264 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____18261 in
                                                     FStar_List.append decls3
                                                       uu____18258 in
                                                   FStar_List.append decls2
                                                     uu____18255 in
                                                 FStar_List.append decls11
                                                   uu____18252 in
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
          let uu____18299 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____18299 with
          | FStar_Pervasives_Native.None  ->
              let uu____18336 = encode_free_var env x t t_norm [] in
              (match uu____18336 with
               | (decls,env1) ->
                   let uu____18363 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____18363 with
                    | (n1,x',uu____18390) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18411) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____18467 = encode_free_var env lid t tt quals in
          match uu____18467 with
          | (decls,env1) ->
              let uu____18486 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____18486
              then
                let uu____18493 =
                  let uu____18496 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____18496 in
                (uu____18493, env1)
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
             (fun uu____18551  ->
                fun lb  ->
                  match uu____18551 with
                  | (decls,env1) ->
                      let uu____18571 =
                        let uu____18578 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____18578
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____18571 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____18600 = FStar_Syntax_Util.head_and_args t in
    match uu____18600 with
    | (hd1,args) ->
        let uu____18649 =
          let uu____18650 = FStar_Syntax_Util.un_uinst hd1 in
          uu____18650.FStar_Syntax_Syntax.n in
        (match uu____18649 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18656,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18679 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18704  ->
      fun quals  ->
        match uu____18704 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____18782 = FStar_Util.first_N nbinders formals in
              match uu____18782 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18865  ->
                         fun uu____18866  ->
                           match (uu____18865, uu____18866) with
                           | ((formal,uu____18884),(binder,uu____18886)) ->
                               let uu____18895 =
                                 let uu____18904 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____18904) in
                               FStar_Syntax_Syntax.NT uu____18895) formals1
                      binders in
                  let extra_formals1 =
                    let uu____18912 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18943  ->
                              match uu____18943 with
                              | (x,i) ->
                                  let uu____18954 =
                                    let uu___145_18955 = x in
                                    let uu____18956 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_18955.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_18955.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18956
                                    } in
                                  (uu____18954, i))) in
                    FStar_All.pipe_right uu____18912
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____18978 =
                      let uu____18981 =
                        let uu____18982 = FStar_Syntax_Subst.subst subst1 t in
                        uu____18982.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____18981 in
                    let uu____18989 =
                      let uu____18990 = FStar_Syntax_Subst.compress body in
                      let uu____18991 =
                        let uu____18992 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18992 in
                      FStar_Syntax_Syntax.extend_app_n uu____18990
                        uu____18991 in
                    uu____18989 uu____18978 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____19055 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____19055
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_19058 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_19058.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_19058.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_19058.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_19058.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_19058.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_19058.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_19058.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_19058.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_19058.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_19058.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_19058.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_19058.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_19058.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_19058.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_19058.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_19058.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_19058.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_19058.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_19058.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_19058.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_19058.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_19058.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_19058.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_19058.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_19058.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_19058.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____19091 = FStar_Syntax_Util.abs_formals e in
                match uu____19091 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____19155::uu____19156 ->
                         let uu____19171 =
                           let uu____19172 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19172.FStar_Syntax_Syntax.n in
                         (match uu____19171 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19223 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19223 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____19265 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____19265
                                   then
                                     let uu____19300 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____19300 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19394  ->
                                                   fun uu____19395  ->
                                                     match (uu____19394,
                                                             uu____19395)
                                                     with
                                                     | ((x,uu____19413),
                                                        (b,uu____19415)) ->
                                                         let uu____19424 =
                                                           let uu____19433 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____19433) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19424)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____19435 =
                                            let uu____19456 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____19456) in
                                          (uu____19435, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19524 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____19524 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19623) ->
                              let uu____19632 =
                                let uu____19653 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____19653 in
                              (uu____19632, true)
                          | uu____19718 when Prims.op_Negation norm1 ->
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
                          | uu____19720 ->
                              let uu____19721 =
                                let uu____19722 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____19723 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19722
                                  uu____19723 in
                              failwith uu____19721)
                     | uu____19748 ->
                         let uu____19749 =
                           let uu____19750 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____19750.FStar_Syntax_Syntax.n in
                         (match uu____19749 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19801 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____19801 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____19833 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____19833 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19926 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____19982 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____19982
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19994 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____20088  ->
                            fun lb  ->
                              match uu____20088 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____20183 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____20183
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____20186 =
                                      let uu____20201 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____20201
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____20186 with
                                    | (tok,decl,env2) ->
                                        let uu____20247 =
                                          let uu____20260 =
                                            let uu____20271 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____20271, tok) in
                                          uu____20260 :: toks in
                                        (uu____20247, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____19994 with
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
                        | uu____20454 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20462 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____20462 vars)
                            else
                              (let uu____20464 =
                                 let uu____20471 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____20471) in
                               FStar_SMTEncoding_Util.mkApp uu____20464) in
                      let uu____20480 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_20484  ->
                                 match uu___116_20484 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____20485 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____20491 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____20491))) in
                      if uu____20480
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____20529;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____20531;
                                FStar_Syntax_Syntax.lbeff = uu____20532;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____20599 =
                                 let uu____20606 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____20606 with
                                 | (tcenv',uu____20626,e_t) ->
                                     let uu____20632 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____20643 -> failwith "Impossible" in
                                     (match uu____20632 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_20659 = env1 in
                                            {
                                              bindings =
                                                (uu___149_20659.bindings);
                                              depth = (uu___149_20659.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_20659.warn);
                                              cache = (uu___149_20659.cache);
                                              nolabels =
                                                (uu___149_20659.nolabels);
                                              use_zfuel_name =
                                                (uu___149_20659.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_20659.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_20659.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____20599 with
                                | (env',e1,t_norm1) ->
                                    let uu____20669 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____20669 with
                                     | ((binders,body,uu____20690,uu____20691),curry)
                                         ->
                                         ((let uu____20702 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____20702
                                           then
                                             let uu____20703 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____20704 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____20703 uu____20704
                                           else ());
                                          (let uu____20706 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____20706 with
                                           | (vars,guards,env'1,binder_decls,uu____20733)
                                               ->
                                               let body1 =
                                                 let uu____20747 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____20747
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____20750 =
                                                 let uu____20759 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____20759
                                                 then
                                                   let uu____20770 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____20771 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____20770, uu____20771)
                                                 else
                                                   (let uu____20781 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____20781)) in
                                               (match uu____20750 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____20804 =
                                                        let uu____20811 =
                                                          let uu____20812 =
                                                            let uu____20823 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____20823) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____20812 in
                                                        let uu____20834 =
                                                          let uu____20837 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____20837 in
                                                        (uu____20811,
                                                          uu____20834,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____20804 in
                                                    let uu____20840 =
                                                      let uu____20843 =
                                                        let uu____20846 =
                                                          let uu____20849 =
                                                            let uu____20852 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____20852 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____20849 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____20846 in
                                                      FStar_List.append
                                                        decls1 uu____20843 in
                                                    (uu____20840, env1))))))
                           | uu____20857 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____20892 = varops.fresh "fuel" in
                             (uu____20892, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____20895 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____20983  ->
                                     fun uu____20984  ->
                                       match (uu____20983, uu____20984) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____21132 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____21132 in
                                           let gtok =
                                             let uu____21134 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____21134 in
                                           let env3 =
                                             let uu____21136 =
                                               let uu____21139 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____21139 in
                                             push_free_var env2 flid gtok
                                               uu____21136 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____20895 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____21297
                                 t_norm uu____21299 =
                                 match (uu____21297, uu____21299) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____21345;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____21346;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____21378 =
                                       let uu____21385 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____21385 with
                                       | (tcenv',uu____21413,e_t) ->
                                           let uu____21419 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____21430 ->
                                                 failwith "Impossible" in
                                           (match uu____21419 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_21446 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_21446.bindings);
                                                    depth =
                                                      (uu___150_21446.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_21446.warn);
                                                    cache =
                                                      (uu___150_21446.cache);
                                                    nolabels =
                                                      (uu___150_21446.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_21446.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_21446.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_21446.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____21378 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____21461 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____21461
                                            then
                                              let uu____21462 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____21463 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____21464 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____21462 uu____21463
                                                uu____21464
                                            else ());
                                           (let uu____21466 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____21466 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____21503 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____21503
                                                  then
                                                    let uu____21504 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____21505 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____21506 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____21507 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____21504 uu____21505
                                                      uu____21506 uu____21507
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____21511 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____21511 with
                                                  | (vars,guards,env'1,binder_decls,uu____21542)
                                                      ->
                                                      let decl_g =
                                                        let uu____21556 =
                                                          let uu____21567 =
                                                            let uu____21570 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____21570 in
                                                          (g, uu____21567,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____21556 in
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
                                                        let uu____21595 =
                                                          let uu____21602 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____21602) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21595 in
                                                      let gsapp =
                                                        let uu____21612 =
                                                          let uu____21619 =
                                                            let uu____21622 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____21622 ::
                                                              vars_tm in
                                                          (g, uu____21619) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21612 in
                                                      let gmax =
                                                        let uu____21628 =
                                                          let uu____21635 =
                                                            let uu____21638 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____21638 ::
                                                              vars_tm in
                                                          (g, uu____21635) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21628 in
                                                      let body1 =
                                                        let uu____21644 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____21644
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____21646 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____21646 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____21664
                                                               =
                                                               let uu____21671
                                                                 =
                                                                 let uu____21672
                                                                   =
                                                                   let uu____21687
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
                                                                    uu____21687) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____21672 in
                                                               let uu____21708
                                                                 =
                                                                 let uu____21711
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____21711 in
                                                               (uu____21671,
                                                                 uu____21708,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21664 in
                                                           let eqn_f =
                                                             let uu____21715
                                                               =
                                                               let uu____21722
                                                                 =
                                                                 let uu____21723
                                                                   =
                                                                   let uu____21734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____21734) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21723 in
                                                               (uu____21722,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21715 in
                                                           let eqn_g' =
                                                             let uu____21748
                                                               =
                                                               let uu____21755
                                                                 =
                                                                 let uu____21756
                                                                   =
                                                                   let uu____21767
                                                                    =
                                                                    let uu____21768
                                                                    =
                                                                    let uu____21773
                                                                    =
                                                                    let uu____21774
                                                                    =
                                                                    let uu____21781
                                                                    =
                                                                    let uu____21784
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____21784
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____21781) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21774 in
                                                                    (gsapp,
                                                                    uu____21773) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____21768 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____21767) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21756 in
                                                               (uu____21755,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21748 in
                                                           let uu____21807 =
                                                             let uu____21816
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____21816
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____21845)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____21870
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____21870
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____21875
                                                                    =
                                                                    let uu____21882
                                                                    =
                                                                    let uu____21883
                                                                    =
                                                                    let uu____21894
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21894) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21883 in
                                                                    (uu____21882,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21875 in
                                                                 let uu____21915
                                                                   =
                                                                   let uu____21922
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____21922
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____21935
                                                                    =
                                                                    let uu____21938
                                                                    =
                                                                    let uu____21939
                                                                    =
                                                                    let uu____21946
                                                                    =
                                                                    let uu____21947
                                                                    =
                                                                    let uu____21958
                                                                    =
                                                                    let uu____21959
                                                                    =
                                                                    let uu____21964
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____21964,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21959 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21958) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21947 in
                                                                    (uu____21946,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21939 in
                                                                    [uu____21938] in
                                                                    (d3,
                                                                    uu____21935) in
                                                                 (match uu____21915
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____21807
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____22029 =
                                 let uu____22042 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____22125  ->
                                      fun uu____22126  ->
                                        match (uu____22125, uu____22126) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____22291 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____22291 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____22042 in
                               (match uu____22029 with
                                | (decls2,eqns,env01) ->
                                    let uu____22364 =
                                      let isDeclFun uu___117_22376 =
                                        match uu___117_22376 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____22377 -> true
                                        | uu____22388 -> false in
                                      let uu____22389 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____22389
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____22364 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22440 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____22440
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
        let uu____22489 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____22489 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____22493 = encode_sigelt' env se in
      match uu____22493 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22509 =
                  let uu____22510 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____22510 in
                [uu____22509]
            | uu____22511 ->
                let uu____22512 =
                  let uu____22515 =
                    let uu____22516 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22516 in
                  uu____22515 :: g in
                let uu____22517 =
                  let uu____22520 =
                    let uu____22521 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____22521 in
                  [uu____22520] in
                FStar_List.append uu____22512 uu____22517 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22534 =
          let uu____22535 = FStar_Syntax_Subst.compress t in
          uu____22535.FStar_Syntax_Syntax.n in
        match uu____22534 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22541)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____22546 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22551 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22556 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22559 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22562 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22577 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22581 =
            let uu____22582 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____22582 Prims.op_Negation in
          if uu____22581
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22616 ->
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
               let uu____22640 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____22640 with
               | (aname,atok,env2) ->
                   let uu____22656 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____22656 with
                    | (formals,uu____22674) ->
                        let uu____22687 =
                          let uu____22692 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____22692 env2 in
                        (match uu____22687 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22704 =
                                 let uu____22705 =
                                   let uu____22716 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22732  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____22716,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____22705 in
                               [uu____22704;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____22745 =
                               let aux uu____22797 uu____22798 =
                                 match (uu____22797, uu____22798) with
                                 | ((bv,uu____22850),(env3,acc_sorts,acc)) ->
                                     let uu____22888 = gen_term_var env3 bv in
                                     (match uu____22888 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____22745 with
                              | (uu____22960,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____22983 =
                                      let uu____22990 =
                                        let uu____22991 =
                                          let uu____23002 =
                                            let uu____23003 =
                                              let uu____23008 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____23008) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____23003 in
                                          ([[app]], xs_sorts, uu____23002) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22991 in
                                      (uu____22990,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22983 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____23028 =
                                      let uu____23035 =
                                        let uu____23036 =
                                          let uu____23047 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____23047) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____23036 in
                                      (uu____23035,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____23028 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____23066 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____23066 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23094,uu____23095)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____23096 = new_term_constant_and_tok_from_lid env lid in
          (match uu____23096 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____23113,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____23119 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_23123  ->
                      match uu___118_23123 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____23124 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____23129 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____23130 -> false)) in
            Prims.op_Negation uu____23119 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____23139 = encode_top_level_val env fv t quals in
             match uu____23139 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____23158 =
                   let uu____23161 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____23161 in
                 (uu____23158, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____23169 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____23169 with
           | (uu____23178,f1) ->
               let uu____23180 = encode_formula f1 env in
               (match uu____23180 with
                | (f2,decls) ->
                    let g =
                      let uu____23194 =
                        let uu____23195 =
                          let uu____23202 =
                            let uu____23205 =
                              let uu____23206 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____23206 in
                            FStar_Pervasives_Native.Some uu____23205 in
                          let uu____23207 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____23202, uu____23207) in
                        FStar_SMTEncoding_Util.mkAssume uu____23195 in
                      [uu____23194] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____23213) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____23225 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____23243 =
                       let uu____23246 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____23246.FStar_Syntax_Syntax.fv_name in
                     uu____23243.FStar_Syntax_Syntax.v in
                   let uu____23247 =
                     let uu____23248 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____23248 in
                   if uu____23247
                   then
                     let val_decl =
                       let uu___151_23276 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_23276.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_23276.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_23276.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____23283 = encode_sigelt' env1 val_decl in
                     match uu____23283 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____23225 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23311,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23313;
                          FStar_Syntax_Syntax.lbtyp = uu____23314;
                          FStar_Syntax_Syntax.lbeff = uu____23315;
                          FStar_Syntax_Syntax.lbdef = uu____23316;_}::[]),uu____23317)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23340 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____23340 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____23369 =
                   let uu____23372 =
                     let uu____23373 =
                       let uu____23380 =
                         let uu____23381 =
                           let uu____23392 =
                             let uu____23393 =
                               let uu____23398 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x]) in
                               (valid_b2t_x, uu____23398) in
                             FStar_SMTEncoding_Util.mkEq uu____23393 in
                           ([[b2t_x]], [xx], uu____23392) in
                         FStar_SMTEncoding_Util.mkForall uu____23381 in
                       (uu____23380,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____23373 in
                   [uu____23372] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23369 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23431,uu____23432) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_23441  ->
                  match uu___119_23441 with
                  | FStar_Syntax_Syntax.Discriminator uu____23442 -> true
                  | uu____23443 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23446,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23457 =
                     let uu____23458 = FStar_List.hd l.FStar_Ident.ns in
                     uu____23458.FStar_Ident.idText in
                   uu____23457 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_23462  ->
                     match uu___120_23462 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23463 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23467) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_23484  ->
                  match uu___121_23484 with
                  | FStar_Syntax_Syntax.Projector uu____23485 -> true
                  | uu____23490 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____23493 = try_lookup_free_var env l in
          (match uu____23493 with
           | FStar_Pervasives_Native.Some uu____23500 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_23504 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_23504.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_23504.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_23504.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23513) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23531) ->
          let uu____23540 = encode_sigelts env ses in
          (match uu____23540 with
           | (g,env1) ->
               let uu____23557 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_23580  ->
                         match uu___122_23580 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23581;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23582;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23583;_}
                             -> false
                         | uu____23586 -> true)) in
               (match uu____23557 with
                | (g',inversions) ->
                    let uu____23601 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_23622  ->
                              match uu___123_23622 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23623 ->
                                  true
                              | uu____23634 -> false)) in
                    (match uu____23601 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23652,tps,k,uu____23655,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_23672  ->
                    match uu___124_23672 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23673 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23682 = c in
              match uu____23682 with
              | (name,args,uu____23687,uu____23688,uu____23689) ->
                  let uu____23694 =
                    let uu____23695 =
                      let uu____23706 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23723  ->
                                match uu____23723 with
                                | (uu____23730,sort,uu____23732) -> sort)) in
                      (name, uu____23706, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____23695 in
                  [uu____23694]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____23759 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23765 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____23765 FStar_Option.isNone)) in
            if uu____23759
            then []
            else
              (let uu____23797 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____23797 with
               | (xxsym,xx) ->
                   let uu____23806 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23845  ->
                             fun l  ->
                               match uu____23845 with
                               | (out,decls) ->
                                   let uu____23865 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____23865 with
                                    | (uu____23876,data_t) ->
                                        let uu____23878 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____23878 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23932 =
                                                 let uu____23933 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____23933.FStar_Syntax_Syntax.n in
                                               match uu____23932 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23948,indices) ->
                                                   indices
                                               | uu____23978 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____24004  ->
                                                         match uu____24004
                                                         with
                                                         | (x,uu____24010) ->
                                                             let uu____24011
                                                               =
                                                               let uu____24012
                                                                 =
                                                                 let uu____24019
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____24019,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____24012 in
                                                             push_term_var
                                                               env1 x
                                                               uu____24011)
                                                    env) in
                                             let uu____24022 =
                                               encode_args indices env1 in
                                             (match uu____24022 with
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
                                                      let uu____24048 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____24064
                                                                 =
                                                                 let uu____24069
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____24069,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____24064)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____24048
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____24072 =
                                                      let uu____24073 =
                                                        let uu____24078 =
                                                          let uu____24079 =
                                                            let uu____24084 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____24084,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____24079 in
                                                        (out, uu____24078) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____24073 in
                                                    (uu____24072,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____23806 with
                    | (data_ax,decls) ->
                        let uu____24097 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____24097 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____24108 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____24108 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____24112 =
                                 let uu____24119 =
                                   let uu____24120 =
                                     let uu____24131 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____24146 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____24131,
                                       uu____24146) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____24120 in
                                 let uu____24161 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____24119,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____24161) in
                               FStar_SMTEncoding_Util.mkAssume uu____24112 in
                             let pattern_guarded_inversion =
                               let uu____24167 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____24167
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____24174 =
                                   let uu____24175 =
                                     let uu____24182 =
                                       let uu____24183 =
                                         let uu____24194 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____24209 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____24194, uu____24209) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____24183 in
                                     let uu____24224 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____24182,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____24224) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____24175 in
                                 [uu____24174]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____24228 =
            let uu____24243 =
              let uu____24244 = FStar_Syntax_Subst.compress k in
              uu____24244.FStar_Syntax_Syntax.n in
            match uu____24243 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____24299 -> (tps, k) in
          (match uu____24228 with
           | (formals,res) ->
               let uu____24326 = FStar_Syntax_Subst.open_term formals res in
               (match uu____24326 with
                | (formals1,res1) ->
                    let uu____24337 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____24337 with
                     | (vars,guards,env',binder_decls,uu____24362) ->
                         let uu____24375 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____24375 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____24394 =
                                  let uu____24401 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____24401) in
                                FStar_SMTEncoding_Util.mkApp uu____24394 in
                              let uu____24410 =
                                let tname_decl =
                                  let uu____24420 =
                                    let uu____24421 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24453  ->
                                              match uu____24453 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____24466 = varops.next_id () in
                                    (tname, uu____24421,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24466, false) in
                                  constructor_or_logic_type_decl uu____24420 in
                                let uu____24475 =
                                  match vars with
                                  | [] ->
                                      let uu____24488 =
                                        let uu____24489 =
                                          let uu____24492 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____24492 in
                                        push_free_var env1 t tname
                                          uu____24489 in
                                      ([], uu____24488)
                                  | uu____24499 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____24508 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24508 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____24522 =
                                          let uu____24529 =
                                            let uu____24530 =
                                              let uu____24545 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24545) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24530 in
                                          (uu____24529,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24522 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____24475 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____24410 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24585 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____24585 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24603 =
                                               let uu____24604 =
                                                 let uu____24611 =
                                                   let uu____24612 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24612 in
                                                 (uu____24611,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24604 in
                                             [uu____24603]
                                           else [] in
                                         let uu____24616 =
                                           let uu____24619 =
                                             let uu____24622 =
                                               let uu____24623 =
                                                 let uu____24630 =
                                                   let uu____24631 =
                                                     let uu____24642 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____24642) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24631 in
                                                 (uu____24630,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24623 in
                                             [uu____24622] in
                                           FStar_List.append karr uu____24619 in
                                         FStar_List.append decls1 uu____24616 in
                                   let aux =
                                     let uu____24658 =
                                       let uu____24661 =
                                         inversion_axioms tapp vars in
                                       let uu____24664 =
                                         let uu____24667 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____24667] in
                                       FStar_List.append uu____24661
                                         uu____24664 in
                                     FStar_List.append kindingAx uu____24658 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24674,uu____24675,uu____24676,uu____24677,uu____24678)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24686,t,uu____24688,n_tps,uu____24690) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____24698 = new_term_constant_and_tok_from_lid env d in
          (match uu____24698 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____24715 = FStar_Syntax_Util.arrow_formals t in
               (match uu____24715 with
                | (formals,t_res) ->
                    let uu____24756 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____24756 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____24770 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____24770 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____24840 =
                                            mk_term_projector_name d x in
                                          (uu____24840,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____24842 =
                                  let uu____24861 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24861, true) in
                                FStar_All.pipe_right uu____24842
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
                              let uu____24900 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____24900 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24912::uu____24913 ->
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
                                         let uu____24958 =
                                           let uu____24969 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24969) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24958
                                     | uu____24994 -> tok_typing in
                                   let uu____25003 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____25003 with
                                    | (vars',guards',env'',decls_formals,uu____25028)
                                        ->
                                        let uu____25041 =
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
                                        (match uu____25041 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____25072 ->
                                                   let uu____25079 =
                                                     let uu____25080 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____25080 in
                                                   [uu____25079] in
                                             let encode_elim uu____25090 =
                                               let uu____25091 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____25091 with
                                               | (head1,args) ->
                                                   let uu____25146 =
                                                     let uu____25147 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____25147.FStar_Syntax_Syntax.n in
                                                   (match uu____25146 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____25159;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____25160;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____25161;_},uu____25162)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25172 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25172
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
                                                                 | uu____25215
                                                                    ->
                                                                    let uu____25216
                                                                    =
                                                                    let uu____25217
                                                                    =
                                                                    let uu____25222
                                                                    =
                                                                    let uu____25223
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25223 in
                                                                    (uu____25222,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25217 in
                                                                    raise
                                                                    uu____25216 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25239
                                                                    =
                                                                    let uu____25240
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25240 in
                                                                    if
                                                                    uu____25239
                                                                    then
                                                                    let uu____25253
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25253]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25255
                                                               =
                                                               let uu____25268
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25320
                                                                     ->
                                                                    fun
                                                                    uu____25321
                                                                     ->
                                                                    match 
                                                                    (uu____25320,
                                                                    uu____25321)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25416
                                                                    =
                                                                    let uu____25423
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25423 in
                                                                    (match uu____25416
                                                                    with
                                                                    | 
                                                                    (uu____25436,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25444
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25444
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25446
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25446
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
                                                                 uu____25268 in
                                                             (match uu____25255
                                                              with
                                                              | (uu____25461,arg_vars,elim_eqns_or_guards,uu____25464)
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
                                                                    let uu____25494
                                                                    =
                                                                    let uu____25501
                                                                    =
                                                                    let uu____25502
                                                                    =
                                                                    let uu____25513
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25524
                                                                    =
                                                                    let uu____25525
                                                                    =
                                                                    let uu____25530
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____25530) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25525 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25513,
                                                                    uu____25524) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25502 in
                                                                    (uu____25501,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25494 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25553
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____25553,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____25555
                                                                    =
                                                                    let uu____25562
                                                                    =
                                                                    let uu____25563
                                                                    =
                                                                    let uu____25574
                                                                    =
                                                                    let uu____25579
                                                                    =
                                                                    let uu____25582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____25582] in
                                                                    [uu____25579] in
                                                                    let uu____25587
                                                                    =
                                                                    let uu____25588
                                                                    =
                                                                    let uu____25593
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____25594
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____25593,
                                                                    uu____25594) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25588 in
                                                                    (uu____25574,
                                                                    [x],
                                                                    uu____25587) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25563 in
                                                                    let uu____25613
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____25562,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25613) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25555
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25620
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
                                                                    (let uu____25648
                                                                    =
                                                                    let uu____25649
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25649
                                                                    dapp1 in
                                                                    [uu____25648]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____25620
                                                                    FStar_List.flatten in
                                                                    let uu____25656
                                                                    =
                                                                    let uu____25663
                                                                    =
                                                                    let uu____25664
                                                                    =
                                                                    let uu____25675
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____25686
                                                                    =
                                                                    let uu____25687
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____25692) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25687 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25675,
                                                                    uu____25686) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25664 in
                                                                    (uu____25663,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25656) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____25713 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____25713
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
                                                                 | uu____25756
                                                                    ->
                                                                    let uu____25757
                                                                    =
                                                                    let uu____25758
                                                                    =
                                                                    let uu____25763
                                                                    =
                                                                    let uu____25764
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25764 in
                                                                    (uu____25763,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____25758 in
                                                                    raise
                                                                    uu____25757 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25780
                                                                    =
                                                                    let uu____25781
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25781 in
                                                                    if
                                                                    uu____25780
                                                                    then
                                                                    let uu____25794
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____25794]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____25796
                                                               =
                                                               let uu____25809
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25861
                                                                     ->
                                                                    fun
                                                                    uu____25862
                                                                     ->
                                                                    match 
                                                                    (uu____25861,
                                                                    uu____25862)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25957
                                                                    =
                                                                    let uu____25964
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25964 in
                                                                    (match uu____25957
                                                                    with
                                                                    | 
                                                                    (uu____25977,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25985
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____25985
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____25987
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
                                                                 uu____25809 in
                                                             (match uu____25796
                                                              with
                                                              | (uu____26002,arg_vars,elim_eqns_or_guards,uu____26005)
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
                                                                    let uu____26035
                                                                    =
                                                                    let uu____26042
                                                                    =
                                                                    let uu____26043
                                                                    =
                                                                    let uu____26054
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____26065
                                                                    =
                                                                    let uu____26066
                                                                    =
                                                                    let uu____26071
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____26071) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26066 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26054,
                                                                    uu____26065) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26043 in
                                                                    (uu____26042,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26035 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____26094
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____26094,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____26096
                                                                    =
                                                                    let uu____26103
                                                                    =
                                                                    let uu____26104
                                                                    =
                                                                    let uu____26115
                                                                    =
                                                                    let uu____26120
                                                                    =
                                                                    let uu____26123
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____26123] in
                                                                    [uu____26120] in
                                                                    let uu____26128
                                                                    =
                                                                    let uu____26129
                                                                    =
                                                                    let uu____26134
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____26135
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____26134,
                                                                    uu____26135) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26129 in
                                                                    (uu____26115,
                                                                    [x],
                                                                    uu____26128) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26104 in
                                                                    let uu____26154
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____26103,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____26154) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26096
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____26161
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
                                                                    (let uu____26189
                                                                    =
                                                                    let uu____26190
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____26190
                                                                    dapp1 in
                                                                    [uu____26189]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____26161
                                                                    FStar_List.flatten in
                                                                    let uu____26197
                                                                    =
                                                                    let uu____26204
                                                                    =
                                                                    let uu____26205
                                                                    =
                                                                    let uu____26216
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____26227
                                                                    =
                                                                    let uu____26228
                                                                    =
                                                                    let uu____26233
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____26233) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____26228 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____26216,
                                                                    uu____26227) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26205 in
                                                                    (uu____26204,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26197) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____26252 ->
                                                        ((let uu____26254 =
                                                            let uu____26255 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____26256 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____26255
                                                              uu____26256 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____26254);
                                                         ([], []))) in
                                             let uu____26261 = encode_elim () in
                                             (match uu____26261 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____26281 =
                                                      let uu____26284 =
                                                        let uu____26287 =
                                                          let uu____26290 =
                                                            let uu____26293 =
                                                              let uu____26294
                                                                =
                                                                let uu____26305
                                                                  =
                                                                  let uu____26308
                                                                    =
                                                                    let uu____26309
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____26309 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____26308 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____26305) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____26294 in
                                                            [uu____26293] in
                                                          let uu____26314 =
                                                            let uu____26317 =
                                                              let uu____26320
                                                                =
                                                                let uu____26323
                                                                  =
                                                                  let uu____26326
                                                                    =
                                                                    let uu____26329
                                                                    =
                                                                    let uu____26332
                                                                    =
                                                                    let uu____26333
                                                                    =
                                                                    let uu____26340
                                                                    =
                                                                    let uu____26341
                                                                    =
                                                                    let uu____26352
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____26352) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26341 in
                                                                    (uu____26340,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26333 in
                                                                    let uu____26365
                                                                    =
                                                                    let uu____26368
                                                                    =
                                                                    let uu____26369
                                                                    =
                                                                    let uu____26376
                                                                    =
                                                                    let uu____26377
                                                                    =
                                                                    let uu____26388
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____26399
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____26388,
                                                                    uu____26399) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____26377 in
                                                                    (uu____26376,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____26369 in
                                                                    [uu____26368] in
                                                                    uu____26332
                                                                    ::
                                                                    uu____26365 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____26329 in
                                                                  FStar_List.append
                                                                    uu____26326
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____26323 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____26320 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____26317 in
                                                          FStar_List.append
                                                            uu____26290
                                                            uu____26314 in
                                                        FStar_List.append
                                                          decls3 uu____26287 in
                                                      FStar_List.append
                                                        decls2 uu____26284 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____26281 in
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
           (fun uu____26445  ->
              fun se  ->
                match uu____26445 with
                | (g,env1) ->
                    let uu____26465 = encode_sigelt env1 se in
                    (match uu____26465 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26524 =
        match uu____26524 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26556 ->
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
                 ((let uu____26562 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____26562
                   then
                     let uu____26563 = FStar_Syntax_Print.bv_to_string x in
                     let uu____26564 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____26565 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26563 uu____26564 uu____26565
                   else ());
                  (let uu____26567 = encode_term t1 env1 in
                   match uu____26567 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____26583 =
                         let uu____26590 =
                           let uu____26591 =
                             let uu____26592 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____26592
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____26591 in
                         new_term_constant_from_string env1 x uu____26590 in
                       (match uu____26583 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____26608 = FStar_Options.log_queries () in
                              if uu____26608
                              then
                                let uu____26611 =
                                  let uu____26612 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____26613 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____26614 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26612 uu____26613 uu____26614 in
                                FStar_Pervasives_Native.Some uu____26611
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26630,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____26644 = encode_free_var env1 fv t t_norm [] in
                 (match uu____26644 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26667,se,uu____26669) ->
                 let uu____26674 = encode_sigelt env1 se in
                 (match uu____26674 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26691,se) ->
                 let uu____26697 = encode_sigelt env1 se in
                 (match uu____26697 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____26714 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____26714 with | (uu____26737,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____26821  ->
            match uu____26821 with
            | (l,uu____26833,uu____26834) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____26880  ->
            match uu____26880 with
            | (l,uu____26894,uu____26895) ->
                let uu____26904 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____26905 =
                  let uu____26908 =
                    let uu____26909 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____26909 in
                  [uu____26908] in
                uu____26904 :: uu____26905)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26925 =
      let uu____26928 =
        let uu____26929 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____26932 =
          let uu____26933 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____26933 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26929;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26932
        } in
      [uu____26928] in
    FStar_ST.write last_env uu____26925
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26944 = FStar_ST.read last_env in
      match uu____26944 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26950 ->
          let uu___153_26953 = e in
          let uu____26954 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_26953.bindings);
            depth = (uu___153_26953.depth);
            tcenv;
            warn = (uu___153_26953.warn);
            cache = (uu___153_26953.cache);
            nolabels = (uu___153_26953.nolabels);
            use_zfuel_name = (uu___153_26953.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_26953.encode_non_total_function_typ);
            current_module_name = uu____26954
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____26959 = FStar_ST.read last_env in
    match uu____26959 with
    | [] -> failwith "Empty env stack"
    | uu____26964::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____26973  ->
    let uu____26974 = FStar_ST.read last_env in
    match uu____26974 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_26987 = hd1 in
          {
            bindings = (uu___154_26987.bindings);
            depth = (uu___154_26987.depth);
            tcenv = (uu___154_26987.tcenv);
            warn = (uu___154_26987.warn);
            cache = refs;
            nolabels = (uu___154_26987.nolabels);
            use_zfuel_name = (uu___154_26987.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_26987.encode_non_total_function_typ);
            current_module_name = (uu___154_26987.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____26993  ->
    let uu____26994 = FStar_ST.read last_env in
    match uu____26994 with
    | [] -> failwith "Popping an empty stack"
    | uu____26999::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____27008  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____27012  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____27016  ->
    let uu____27017 = FStar_ST.read last_env in
    match uu____27017 with
    | hd1::uu____27023::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____27029 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
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
        | (uu____27094::uu____27095,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_27103 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_27103.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_27103.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_27103.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27104 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____27121 =
        let uu____27124 =
          let uu____27125 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____27125 in
        let uu____27126 = open_fact_db_tags env in uu____27124 :: uu____27126 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27121
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
      let uu____27150 = encode_sigelt env se in
      match uu____27150 with
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
        let uu____27188 = FStar_Options.log_queries () in
        if uu____27188
        then
          let uu____27191 =
            let uu____27192 =
              let uu____27193 =
                let uu____27194 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____27194 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____27193 in
            FStar_SMTEncoding_Term.Caption uu____27192 in
          uu____27191 :: decls
        else decls in
      let env =
        let uu____27205 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27205 tcenv in
      let uu____27206 = encode_top_level_facts env se in
      match uu____27206 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____27220 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____27220))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____27234 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____27234
       then
         let uu____27235 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27235
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27270  ->
                 fun se  ->
                   match uu____27270 with
                   | (g,env2) ->
                       let uu____27290 = encode_top_level_facts env2 se in
                       (match uu____27290 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____27313 =
         encode_signature
           (let uu___156_27322 = env in
            {
              bindings = (uu___156_27322.bindings);
              depth = (uu___156_27322.depth);
              tcenv = (uu___156_27322.tcenv);
              warn = false;
              cache = (uu___156_27322.cache);
              nolabels = (uu___156_27322.nolabels);
              use_zfuel_name = (uu___156_27322.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_27322.encode_non_total_function_typ);
              current_module_name = (uu___156_27322.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____27313 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27339 = FStar_Options.log_queries () in
             if uu____27339
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_27347 = env1 in
               {
                 bindings = (uu___157_27347.bindings);
                 depth = (uu___157_27347.depth);
                 tcenv = (uu___157_27347.tcenv);
                 warn = true;
                 cache = (uu___157_27347.cache);
                 nolabels = (uu___157_27347.nolabels);
                 use_zfuel_name = (uu___157_27347.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_27347.encode_non_total_function_typ);
                 current_module_name = (uu___157_27347.current_module_name)
               });
            (let uu____27349 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____27349
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
        (let uu____27404 =
           let uu____27405 = FStar_TypeChecker_Env.current_module tcenv in
           uu____27405.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27404);
        (let env =
           let uu____27407 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____27407 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____27419 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27454 = aux rest in
                 (match uu____27454 with
                  | (out,rest1) ->
                      let t =
                        let uu____27486 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____27486 with
                        | FStar_Pervasives_Native.Some uu____27493 ->
                            let uu____27494 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____27494
                              x.FStar_Syntax_Syntax.sort
                        | uu____27495 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____27499 =
                        let uu____27502 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_27505 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_27505.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_27505.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____27502 :: out in
                      (uu____27499, rest1))
             | uu____27510 -> ([], bindings1) in
           let uu____27517 = aux bindings in
           match uu____27517 with
           | (closing,bindings1) ->
               let uu____27542 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____27542, bindings1) in
         match uu____27419 with
         | (q1,bindings1) ->
             let uu____27565 =
               let uu____27570 =
                 FStar_List.filter
                   (fun uu___125_27575  ->
                      match uu___125_27575 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27576 ->
                          false
                      | uu____27583 -> true) bindings1 in
               encode_env_bindings env uu____27570 in
             (match uu____27565 with
              | (env_decls,env1) ->
                  ((let uu____27601 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____27601
                    then
                      let uu____27602 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27602
                    else ());
                   (let uu____27604 = encode_formula q1 env1 in
                    match uu____27604 with
                    | (phi,qdecls) ->
                        let uu____27625 =
                          let uu____27630 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27630 phi in
                        (match uu____27625 with
                         | (labels,phi1) ->
                             let uu____27647 = encode_labels labels in
                             (match uu____27647 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____27684 =
                                      let uu____27691 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____27692 =
                                        varops.mk_unique "@query" in
                                      (uu____27691,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27692) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27684 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____27711 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____27711 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27713 = encode_formula q env in
       match uu____27713 with
       | (f,uu____27719) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27721) -> true
             | uu____27726 -> false)))