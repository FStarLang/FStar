open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____47 = match uu____47 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___102_89  ->
       match uu___102_89 with
       | (FStar_Util.Inl uu____94,uu____95) -> false
       | uu____98 -> true) args
let subst_lcomp_opt s l =
  match l with
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
      let uu____132 =
        let uu____135 =
          let uu____136 =
            let uu____138 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____138 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____136 in
        FStar_Util.Inl uu____135 in
      FStar_Pervasives_Native.Some uu____132
  | uu____142 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_159 = a in
        let uu____160 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____160;
          FStar_Syntax_Syntax.index =
            (uu___126_159.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_159.FStar_Syntax_Syntax.sort)
        } in
      let uu____161 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____161
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____177 =
          let uu____178 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____178 in
        let uu____179 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____179 with
        | (uu____182,t) ->
            let uu____184 =
              let uu____185 = FStar_Syntax_Subst.compress t in
              uu____185.FStar_Syntax_Syntax.n in
            (match uu____184 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____197 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____197 with
                  | (binders,uu____201) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____214 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____223 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____223
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____232 =
        let uu____235 = mk_term_projector_name lid a in
        (uu____235,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____232
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____244 =
        let uu____247 = mk_term_projector_name_by_pos lid i in
        (uu____247,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____244
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
  let new_scope uu____861 =
    let uu____862 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____864 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____862, uu____864) in
  let scopes =
    let uu____875 = let uu____881 = new_scope () in [uu____881] in
    FStar_Util.mk_ref uu____875 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____906 =
        let uu____908 = FStar_ST.read scopes in
        FStar_Util.find_map uu____908
          (fun uu____928  ->
             match uu____928 with
             | (names1,uu____935) -> FStar_Util.smap_try_find names1 y1) in
      match uu____906 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____940 ->
          (FStar_Util.incr ctr;
           (let uu____945 =
              let uu____946 =
                let uu____947 = FStar_ST.read ctr in
                Prims.string_of_int uu____947 in
              Prims.strcat "__" uu____946 in
            Prims.strcat y1 uu____945)) in
    let top_scope =
      let uu____952 =
        let uu____957 = FStar_ST.read scopes in FStar_List.hd uu____957 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____952 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____996 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____1007 =
      let uu____1008 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1008 in
    FStar_Util.format2 "%s_%s" pfx uu____1007 in
  let string_const s =
    let uu____1013 =
      let uu____1015 = FStar_ST.read scopes in
      FStar_Util.find_map uu____1015
        (fun uu____1035  ->
           match uu____1035 with
           | (uu____1041,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1013 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1050 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1050 in
        let top_scope =
          let uu____1053 =
            let uu____1058 = FStar_ST.read scopes in FStar_List.hd uu____1058 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1053 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1086 =
    let uu____1087 =
      let uu____1093 = new_scope () in
      let uu____1098 = FStar_ST.read scopes in uu____1093 :: uu____1098 in
    FStar_ST.write scopes uu____1087 in
  let pop1 uu____1125 =
    let uu____1126 =
      let uu____1132 = FStar_ST.read scopes in FStar_List.tl uu____1132 in
    FStar_ST.write scopes uu____1126 in
  let mark1 uu____1159 = push1 () in
  let reset_mark1 uu____1163 = pop1 () in
  let commit_mark1 uu____1167 =
    let uu____1168 = FStar_ST.read scopes in
    match uu____1168 with
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
    | uu____1234 -> failwith "Impossible" in
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
    let uu___127_1244 = x in
    let uu____1245 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1245;
      FStar_Syntax_Syntax.index = (uu___127_1244.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1244.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1269 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1295 -> false
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
         (fun uu___103_1621  ->
            match uu___103_1621 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1624 -> [])) in
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
    let uu____1634 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_1641  ->
              match uu___104_1641 with
              | Binding_var (x,uu____1643) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1645,uu____1646,uu____1647) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1634 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____1685 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1685
      then
        let uu____1687 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____1687
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
      let uu____1700 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1700)
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
        (let uu___128_1715 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1715.tcenv);
           warn = (uu___128_1715.warn);
           cache = (uu___128_1715.cache);
           nolabels = (uu___128_1715.nolabels);
           use_zfuel_name = (uu___128_1715.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1715.encode_non_total_function_typ);
           current_module_name = (uu___128_1715.current_module_name)
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
        (let uu___129_1731 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1731.depth);
           tcenv = (uu___129_1731.tcenv);
           warn = (uu___129_1731.warn);
           cache = (uu___129_1731.cache);
           nolabels = (uu___129_1731.nolabels);
           use_zfuel_name = (uu___129_1731.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1731.encode_non_total_function_typ);
           current_module_name = (uu___129_1731.current_module_name)
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
          (let uu___130_1751 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1751.depth);
             tcenv = (uu___130_1751.tcenv);
             warn = (uu___130_1751.warn);
             cache = (uu___130_1751.cache);
             nolabels = (uu___130_1751.nolabels);
             use_zfuel_name = (uu___130_1751.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1751.encode_non_total_function_typ);
             current_module_name = (uu___130_1751.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1764 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1764.depth);
          tcenv = (uu___131_1764.tcenv);
          warn = (uu___131_1764.warn);
          cache = (uu___131_1764.cache);
          nolabels = (uu___131_1764.nolabels);
          use_zfuel_name = (uu___131_1764.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1764.encode_non_total_function_typ);
          current_module_name = (uu___131_1764.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1785  ->
             match uu___105_1785 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____1793 -> FStar_Pervasives_Native.None) in
      let uu____1796 = aux a in
      match uu____1796 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____1803 = aux a2 in
          (match uu____1803 with
           | FStar_Pervasives_Native.None  ->
               let uu____1809 =
                 let uu____1810 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1811 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1810 uu____1811 in
               failwith uu____1809
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
      let uu____1833 =
        let uu___132_1834 = env in
        let uu____1835 =
          let uu____1837 =
            let uu____1838 =
              let uu____1845 =
                let uu____1847 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                  uu____1847 in
              (x, fname, uu____1845, FStar_Pervasives_Native.None) in
            Binding_fvar uu____1838 in
          uu____1837 :: (env.bindings) in
        {
          bindings = uu____1835;
          depth = (uu___132_1834.depth);
          tcenv = (uu___132_1834.tcenv);
          warn = (uu___132_1834.warn);
          cache = (uu___132_1834.cache);
          nolabels = (uu___132_1834.nolabels);
          use_zfuel_name = (uu___132_1834.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1834.encode_non_total_function_typ);
          current_module_name = (uu___132_1834.current_module_name)
        } in
      (fname, ftok, uu____1833)
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
        (fun uu___106_1876  ->
           match uu___106_1876 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____1898 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1912 =
        lookup_binding env
          (fun uu___107_1919  ->
             match uu___107_1919 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____1929 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____1912 FStar_Option.isSome
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
      let uu____1944 = try_lookup_lid env a in
      match uu____1944 with
      | FStar_Pervasives_Native.None  ->
          let uu____1961 =
            let uu____1962 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1962 in
          failwith uu____1961
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
          let uu___133_1997 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_1997.depth);
            tcenv = (uu___133_1997.tcenv);
            warn = (uu___133_1997.warn);
            cache = (uu___133_1997.cache);
            nolabels = (uu___133_1997.nolabels);
            use_zfuel_name = (uu___133_1997.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1997.encode_non_total_function_typ);
            current_module_name = (uu___133_1997.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2012 = lookup_lid env x in
        match uu____2012 with
        | (t1,t2,uu____2020) ->
            let t3 =
              let uu____2026 =
                let uu____2030 =
                  let uu____2032 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2032] in
                (f, uu____2030) in
              FStar_SMTEncoding_Util.mkApp uu____2026 in
            let uu___134_2035 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_2035.depth);
              tcenv = (uu___134_2035.tcenv);
              warn = (uu___134_2035.warn);
              cache = (uu___134_2035.cache);
              nolabels = (uu___134_2035.nolabels);
              use_zfuel_name = (uu___134_2035.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_2035.encode_non_total_function_typ);
              current_module_name = (uu___134_2035.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2047 = try_lookup_lid env l in
      match uu____2047 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2074 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2079,fuel::[]) ->
                         let uu____2082 =
                           let uu____2083 =
                             let uu____2084 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2084
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2083 "fuel" in
                         if uu____2082
                         then
                           let uu____2086 =
                             let uu____2087 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2087
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2086
                         else FStar_Pervasives_Native.Some t
                     | uu____2090 -> FStar_Pervasives_Native.Some t)
                | uu____2091 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2103 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2103 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2106 =
            let uu____2107 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2107 in
          failwith uu____2106
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2118 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2118 with | (x,uu____2125,uu____2126) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2144 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2144 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2165;
                 FStar_SMTEncoding_Term.rng = uu____2166;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2174 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2188 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___108_2204  ->
           match uu___108_2204 with
           | Binding_fvar (uu____2206,nm',tok,uu____2209) when nm = nm' ->
               tok
           | uu____2214 -> FStar_Pervasives_Native.None)
let mkForall_fuel' n1 uu____2234 =
  match uu____2234 with
  | (pats,vars,body) ->
      let fallback uu____2250 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2253 = FStar_Options.unthrottle_inductives () in
      if uu____2253
      then fallback ()
      else
        (let uu____2255 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2255 with
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
                       | uu____2276 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2290 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2290
                     | uu____2292 ->
                         let uu____2293 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2293 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2296 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____2325 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2332 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2336 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2337 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2346 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2355 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2357 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2357 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____2367;
             FStar_Syntax_Syntax.vars = uu____2368;_},uu____2369)
          ->
          let uu____2380 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2380 FStar_Option.isNone
      | uu____2389 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2398 =
        let uu____2399 = FStar_Syntax_Util.un_uinst t in
        uu____2399.FStar_Syntax_Syntax.n in
      match uu____2398 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2401,uu____2402,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_2414  ->
                  match uu___109_2414 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2415 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2417 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2417 FStar_Option.isSome
      | uu____2426 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2435 = head_normal env t in
      if uu____2435
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
    let uu____2449 =
      let uu____2450 = FStar_Syntax_Syntax.null_binder t in [uu____2450] in
    let uu____2451 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____2449 uu____2451 FStar_Pervasives_Native.None
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
                    let uu____2478 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2478
                | s ->
                    let uu____2482 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2482) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_2497  ->
    match uu___110_2497 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2498 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2529;
                       FStar_SMTEncoding_Term.rng = uu____2530;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2544) ->
              let uu____2549 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2566 -> false) args (FStar_List.rev xs)) in
              if uu____2549
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____2569,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2572 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2576 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2576)) in
              if uu____2572
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____2579 -> FStar_Pervasives_Native.None in
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
    | uu____2746 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2750  ->
    match uu___111_2750 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2752 =
          let uu____2756 =
            let uu____2758 =
              let uu____2759 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2759 in
            [uu____2758] in
          ("FStar.Char.Char", uu____2756) in
        FStar_SMTEncoding_Util.mkApp uu____2752
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____2767 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2767
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____2769) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2778) ->
        let uu____2781 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2781
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2785 =
          let uu____2786 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2786 in
        failwith uu____2785
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2805 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2812 ->
            let uu____2816 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2816
        | uu____2817 ->
            if norm1
            then let uu____2818 = whnf env t1 in aux false uu____2818
            else
              (let uu____2820 =
                 let uu____2821 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2822 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2821 uu____2822 in
               failwith uu____2820) in
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
    | uu____2842 ->
        let uu____2843 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2843)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2870::uu____2871::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2874::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____2876 -> false
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
        (let uu____3013 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3013
         then
           let uu____3014 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3014
         else ());
        (let uu____3016 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3065  ->
                   fun b  ->
                     match uu____3065 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3108 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3117 = gen_term_var env1 x in
                           match uu____3117 with
                           | (xxsym,xx,env') ->
                               let uu____3131 =
                                 let uu____3134 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3134 env1 xx in
                               (match uu____3131 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3108 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3016 with
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
          let uu____3222 = encode_term t env in
          match uu____3222 with
          | (t1,decls) ->
              let uu____3229 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3229, decls)
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
          let uu____3237 = encode_term t env in
          match uu____3237 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3246 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3246, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3248 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3248, decls))
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
        let uu____3253 = encode_args args_e env in
        match uu____3253 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3265 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3272 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3272 in
            let binary arg_tms1 =
              let uu____3281 =
                let uu____3282 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3282 in
              let uu____3283 =
                let uu____3284 =
                  let uu____3285 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3285 in
                FStar_SMTEncoding_Term.unboxInt uu____3284 in
              (uu____3281, uu____3283) in
            let mk_default uu____3290 =
              let uu____3291 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3291 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3332 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3332
              then
                let uu____3333 = let uu____3334 = mk_args ts in op uu____3334 in
                FStar_All.pipe_right uu____3333 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3357 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3357
              then
                let uu____3358 = binary ts in
                match uu____3358 with
                | (t1,t2) ->
                    let uu____3363 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3363
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3366 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3366
                 then
                   let uu____3367 = op (binary ts) in
                   FStar_All.pipe_right uu____3367
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
            let uu____3457 =
              let uu____3463 =
                FStar_List.tryFind
                  (fun uu____3478  ->
                     match uu____3478 with
                     | (l,uu____3485) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3463 FStar_Util.must in
            (match uu____3457 with
             | (uu____3510,op) ->
                 let uu____3518 = op arg_tms in (uu____3518, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3525 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3525
       then
         let uu____3526 = FStar_Syntax_Print.tag_of_term t in
         let uu____3527 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3528 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3526 uu____3527
           uu____3528
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3532 ->
           let uu____3545 =
             let uu____3546 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3547 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3548 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3549 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3546
               uu____3547 uu____3548 uu____3549 in
           failwith uu____3545
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3552 =
             let uu____3553 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3554 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3555 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3556 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3553
               uu____3554 uu____3555 uu____3556 in
           failwith uu____3552
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3560 =
             let uu____3561 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3561 in
           failwith uu____3560
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3566) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3588) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3595 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3595, [])
       | FStar_Syntax_Syntax.Tm_type uu____3597 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3600) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3604 = encode_const c in (uu____3604, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3617 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3617 with
            | (binders1,res) ->
                let uu____3624 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3624
                then
                  let uu____3627 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____3627 with
                   | (vars,guards,env',decls,uu____3642) ->
                       let fsym =
                         let uu____3652 = varops.fresh "f" in
                         (uu____3652, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3655 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3661 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3661.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3661.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3661.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3661.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3661.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3661.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3661.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3661.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3661.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3661.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3661.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3661.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3661.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3661.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3661.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3661.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3661.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3661.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3661.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3661.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3661.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3661.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3661.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3661.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3661.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3661.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3655 with
                        | (pre_opt,res_t) ->
                            let uu____3668 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____3668 with
                             | (res_pred,decls') ->
                                 let uu____3675 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3682 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3682, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3685 =
                                         encode_formula pre env' in
                                       (match uu____3685 with
                                        | (guard,decls0) ->
                                            let uu____3693 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3693, decls0)) in
                                 (match uu____3675 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3701 =
                                          let uu____3707 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3707) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3701 in
                                      let cvars =
                                        let uu____3717 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3717
                                          (FStar_List.filter
                                             (fun uu____3726  ->
                                                match uu____3726 with
                                                | (x,uu____3730) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3741 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3741 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3746 =
                                             let uu____3747 =
                                               let uu____3751 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3751) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3747 in
                                           (uu____3746,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3762 =
                                               let uu____3763 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3763 in
                                             varops.mk_unique uu____3762 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____3770 =
                                               FStar_Options.log_queries () in
                                             if uu____3770
                                             then
                                               let uu____3772 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3772
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3778 =
                                               let uu____3782 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3782) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3778 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3790 =
                                               let uu____3794 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3794,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3790 in
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
                                             let uu____3807 =
                                               let uu____3811 =
                                                 let uu____3812 =
                                                   let uu____3818 =
                                                     let uu____3819 =
                                                       let uu____3822 =
                                                         let uu____3823 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3823 in
                                                       (f_has_t, uu____3822) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3819 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3818) in
                                                 mkForall_fuel uu____3812 in
                                               (uu____3811,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3807 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3836 =
                                               let uu____3840 =
                                                 let uu____3841 =
                                                   let uu____3847 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3847) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3841 in
                                               (uu____3840,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3836 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3861 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3861);
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
                     let uu____3872 =
                       let uu____3876 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3876,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3872 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3885 =
                       let uu____3889 =
                         let uu____3890 =
                           let uu____3896 =
                             let uu____3897 =
                               let uu____3900 =
                                 let uu____3901 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3901 in
                               (f_has_t, uu____3900) in
                             FStar_SMTEncoding_Util.mkImp uu____3897 in
                           ([[f_has_t]], [fsym], uu____3896) in
                         mkForall_fuel uu____3890 in
                       (uu____3889, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3885 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3915 ->
           let uu____3919 =
             let uu____3922 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3922 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____3927;
                 FStar_Syntax_Syntax.vars = uu____3928;_} ->
                 let uu____3932 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____3932 with
                  | (b,f1) ->
                      let uu____3946 =
                        let uu____3947 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____3947 in
                      (uu____3946, f1))
             | uu____3952 -> failwith "impossible" in
           (match uu____3919 with
            | (x,f) ->
                let uu____3959 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3959 with
                 | (base_t,decls) ->
                     let uu____3966 = gen_term_var env x in
                     (match uu____3966 with
                      | (x1,xtm,env') ->
                          let uu____3975 = encode_formula f env' in
                          (match uu____3975 with
                           | (refinement,decls') ->
                               let uu____3982 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3982 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3993 =
                                        let uu____3995 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3999 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3995
                                          uu____3999 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3993 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4018  ->
                                              match uu____4018 with
                                              | (y,uu____4022) ->
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
                                    let uu____4041 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4041 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4046 =
                                           let uu____4047 =
                                             let uu____4051 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4051) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4047 in
                                         (uu____4046,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4063 =
                                             let uu____4064 =
                                               let uu____4065 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4065 in
                                             Prims.strcat module_name
                                               uu____4064 in
                                           varops.mk_unique uu____4063 in
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
                                           let uu____4074 =
                                             let uu____4078 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4078) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4074 in
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
                                           let uu____4089 =
                                             let uu____4093 =
                                               let uu____4094 =
                                                 let uu____4100 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4100) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4094 in
                                             (uu____4093,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4089 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4115 =
                                             let uu____4119 =
                                               let uu____4120 =
                                                 let uu____4126 =
                                                   let uu____4127 =
                                                     let uu____4130 =
                                                       let uu____4131 =
                                                         let uu____4137 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4137) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4131 in
                                                     (uu____4130, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4127 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4126) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4120 in
                                             (uu____4119,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4115 in
                                         let t_kinding =
                                           let uu____4157 =
                                             let uu____4161 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4161,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4157 in
                                         let t_interp =
                                           let uu____4171 =
                                             let uu____4175 =
                                               let uu____4176 =
                                                 let uu____4182 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4182) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4176 in
                                             let uu____4194 =
                                               let uu____4196 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4196 in
                                             (uu____4175, uu____4194,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4171 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4201 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4201);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4218 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4218 in
           let uu____4219 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4219 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4227 =
                    let uu____4231 =
                      let uu____4232 =
                        let uu____4233 =
                          let uu____4234 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4234 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4233 in
                      varops.mk_unique uu____4232 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4231) in
                  FStar_SMTEncoding_Util.mkAssume uu____4227 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4237 ->
           let uu____4245 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4245 with
            | (head1,args_e) ->
                let uu____4267 =
                  let uu____4274 =
                    let uu____4275 = FStar_Syntax_Subst.compress head1 in
                    uu____4275.FStar_Syntax_Syntax.n in
                  (uu____4274, args_e) in
                (match uu____4267 with
                 | uu____4283 when head_redex env head1 ->
                     let uu____4290 = whnf env t in
                     encode_term uu____4290 env
                 | uu____4291 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____4302;
                       FStar_Syntax_Syntax.vars = uu____4303;_},uu____4304),uu____4305::
                    (v1,uu____4307)::(v2,uu____4309)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4335 = encode_term v1 env in
                     (match uu____4335 with
                      | (v11,decls1) ->
                          let uu____4342 = encode_term v2 env in
                          (match uu____4342 with
                           | (v21,decls2) ->
                               let uu____4349 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4349,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4352::(v1,uu____4354)::(v2,uu____4356)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4380 = encode_term v1 env in
                     (match uu____4380 with
                      | (v11,decls1) ->
                          let uu____4387 = encode_term v2 env in
                          (match uu____4387 with
                           | (v21,decls2) ->
                               let uu____4394 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4394,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4396) ->
                     let e0 =
                       let uu____4406 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4406 in
                     ((let uu____4411 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4411
                       then
                         let uu____4412 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4412
                       else ());
                      (let e =
                         let uu____4416 =
                           let uu____4417 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4418 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4417
                             uu____4418 in
                         uu____4416 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4426),(arg,uu____4428)::[]) -> encode_term arg env
                 | uu____4441 ->
                     let uu____4448 = encode_args args_e env in
                     (match uu____4448 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4479 = encode_term head1 env in
                            match uu____4479 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____4514 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4514 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4562  ->
                                                 fun uu____4563  ->
                                                   match (uu____4562,
                                                           uu____4563)
                                                   with
                                                   | ((bv,uu____4575),
                                                      (a,uu____4577)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4587 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4587
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4590 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____4590 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4600 =
                                                   let uu____4604 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4609 =
                                                     let uu____4610 =
                                                       let uu____4611 =
                                                         let uu____4612 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4612 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4611 in
                                                     varops.mk_unique
                                                       uu____4610 in
                                                   (uu____4604,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____4609) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4600 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4623 = lookup_free_var_sym env fv in
                            match uu____4623 with
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
                                   FStar_Syntax_Syntax.pos = uu____4642;
                                   FStar_Syntax_Syntax.vars = uu____4643;_},uu____4644)
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
                                   FStar_Syntax_Syntax.pos = uu____4651;
                                   FStar_Syntax_Syntax.vars = uu____4652;_},uu____4653)
                                ->
                                let uu____4656 =
                                  let uu____4657 =
                                    let uu____4660 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4660
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4657
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4656
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4676 =
                                  let uu____4677 =
                                    let uu____4680 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4680
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4677
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4676
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4695,(FStar_Util.Inl t1,uu____4697),uu____4698)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4723,(FStar_Util.Inr c,uu____4725),uu____4726)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____4751 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____4766 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4766 in
                               let uu____4767 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4767 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4777;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4778;_},uu____4779)
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
                                     | uu____4803 ->
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
           let uu____4840 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4840 with
            | (bs1,body1,opening) ->
                let fallback uu____4855 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____4860 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4860, [decl]) in
                let is_impure rc =
                  let uu____4866 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____4866 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____4874 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4874
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____4885 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____4885
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____4888 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____4888)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____4893 =
                         let uu____4894 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4894 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4893);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____4896 =
                       (is_impure rc) &&
                         (let uu____4898 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____4898) in
                     if uu____4896
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4903 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____4903 with
                        | (vars,guards,envbody,decls,uu____4918) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____4926 = encode_term body2 envbody in
                            (match uu____4926 with
                             | (body3,decls') ->
                                 let uu____4933 =
                                   let uu____4938 = codomain_eff rc in
                                   match uu____4938 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____4949 = encode_term tfun env in
                                       (match uu____4949 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____4933 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____4968 =
                                          let uu____4974 =
                                            let uu____4975 =
                                              let uu____4978 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4978, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4975 in
                                          ([], vars, uu____4974) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4968 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____4986 =
                                              let uu____4988 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____4988
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____4986 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4999 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4999 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5004 =
                                             let uu____5005 =
                                               let uu____5009 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5009) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5005 in
                                           (uu____5004,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5015 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5015 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5022 =
                                                    let uu____5023 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5023 = cache_size in
                                                  if uu____5022
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
                                                    let uu____5034 =
                                                      let uu____5035 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5035 in
                                                    varops.mk_unique
                                                      uu____5034 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5040 =
                                                    let uu____5044 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5044) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5040 in
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
                                                      let uu____5056 =
                                                        let uu____5057 =
                                                          let uu____5061 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5061,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5057 in
                                                      [uu____5056] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5069 =
                                                    let uu____5073 =
                                                      let uu____5074 =
                                                        let uu____5080 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5080) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5074 in
                                                    (uu____5073,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5069 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5090 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5090);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5092,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5093;
                          FStar_Syntax_Syntax.lbunivs = uu____5094;
                          FStar_Syntax_Syntax.lbtyp = uu____5095;
                          FStar_Syntax_Syntax.lbeff = uu____5096;
                          FStar_Syntax_Syntax.lbdef = uu____5097;_}::uu____5098),uu____5099)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5113;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5115;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5127 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5139 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5139, [decl_e])))
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
              let uu____5173 = encode_term e1 env in
              match uu____5173 with
              | (ee1,decls1) ->
                  let uu____5180 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____5180 with
                   | (xs,e21) ->
                       let uu____5194 = FStar_List.hd xs in
                       (match uu____5194 with
                        | (x1,uu____5202) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5204 = encode_body e21 env' in
                            (match uu____5204 with
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
            let uu____5226 =
              let uu____5230 =
                let uu____5231 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5231 in
              gen_term_var env uu____5230 in
            match uu____5226 with
            | (scrsym,scr',env1) ->
                let uu____5240 = encode_term e env1 in
                (match uu____5240 with
                 | (scr,decls) ->
                     let uu____5247 =
                       let encode_branch b uu____5263 =
                         match uu____5263 with
                         | (else_case,decls1) ->
                             let uu____5274 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5274 with
                              | (p,w,br) ->
                                  let uu____5289 = encode_pat env1 p in
                                  (match uu____5289 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5313  ->
                                                   match uu____5313 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5318 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____5330 =
                                               encode_term w1 env2 in
                                             (match uu____5330 with
                                              | (w2,decls2) ->
                                                  let uu____5338 =
                                                    let uu____5339 =
                                                      let uu____5342 =
                                                        let uu____5343 =
                                                          let uu____5346 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5346) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5343 in
                                                      (guard, uu____5342) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5339 in
                                                  (uu____5338, decls2)) in
                                       (match uu____5318 with
                                        | (guard1,decls2) ->
                                            let uu____5354 =
                                              encode_br br env2 in
                                            (match uu____5354 with
                                             | (br1,decls3) ->
                                                 let uu____5362 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5362,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5247 with
                      | (match_tm,decls1) ->
                          let uu____5373 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5373, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____5395 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5395
       then
         let uu____5396 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5396
       else ());
      (let uu____5398 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5398 with
       | (vars,pat_term) ->
           let uu____5408 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5439  ->
                     fun v1  ->
                       match uu____5439 with
                       | (env1,vars1) ->
                           let uu____5467 = gen_term_var env1 v1 in
                           (match uu____5467 with
                            | (xx,uu____5479,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5408 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5524 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5525 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5526 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5531 =
                        let uu____5534 = encode_const c in
                        (scrutinee, uu____5534) in
                      FStar_SMTEncoding_Util.mkEq uu____5531
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5547 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5547 with
                        | (uu____5551,uu____5552::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5554 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5575  ->
                                  match uu____5575 with
                                  | (arg,uu____5580) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5584 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5584)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5602) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5619 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5632 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5658  ->
                                  match uu____5658 with
                                  | (arg,uu____5666) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5670 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5670)) in
                      FStar_All.pipe_right uu____5632 FStar_List.flatten in
                let pat_term1 uu____5686 = encode_term pat_term env1 in
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
      let uu____5693 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5717  ->
                fun uu____5718  ->
                  match (uu____5717, uu____5718) with
                  | ((tms,decls),(t,uu____5738)) ->
                      let uu____5749 = encode_term t env in
                      (match uu____5749 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5693 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5783 = FStar_Syntax_Util.list_elements e in
        match uu____5783 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5797 =
          let uu____5805 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5805 FStar_Syntax_Util.head_and_args in
        match uu____5797 with
        | (head1,args) ->
            let uu____5826 =
              let uu____5833 =
                let uu____5834 = FStar_Syntax_Util.un_uinst head1 in
                uu____5834.FStar_Syntax_Syntax.n in
              (uu____5833, args) in
            (match uu____5826 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5842,uu____5843)::(e,uu____5845)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____5863 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5886 =
            let uu____5894 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5894 FStar_Syntax_Util.head_and_args in
          match uu____5886 with
          | (head1,args) ->
              let uu____5916 =
                let uu____5923 =
                  let uu____5924 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5924.FStar_Syntax_Syntax.n in
                (uu____5923, args) in
              (match uu____5916 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5934)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____5948 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____5960 = smt_pat_or1 t1 in
            (match uu____5960 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____5969 = list_elements1 e in
                 FStar_All.pipe_right uu____5969
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5980 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5980
                           (FStar_List.map one_pat)))
             | uu____5986 ->
                 let uu____5989 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5989])
        | uu____6000 ->
            let uu____6002 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6002] in
      let uu____6013 =
        let uu____6023 =
          let uu____6024 = FStar_Syntax_Subst.compress t in
          uu____6024.FStar_Syntax_Syntax.n in
        match uu____6023 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6045 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6045 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6068;
                        FStar_Syntax_Syntax.effect_name = uu____6069;
                        FStar_Syntax_Syntax.result_typ = uu____6070;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6072)::(post,uu____6074)::(pats,uu____6076)::[];
                        FStar_Syntax_Syntax.flags = uu____6077;_}
                      ->
                      let uu____6098 = lemma_pats pats in
                      (binders1, pre, post, uu____6098)
                  | uu____6107 -> failwith "impos"))
        | uu____6117 -> failwith "Impos" in
      match uu____6013 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6144 = env in
            {
              bindings = (uu___136_6144.bindings);
              depth = (uu___136_6144.depth);
              tcenv = (uu___136_6144.tcenv);
              warn = (uu___136_6144.warn);
              cache = (uu___136_6144.cache);
              nolabels = (uu___136_6144.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6144.encode_non_total_function_typ);
              current_module_name = (uu___136_6144.current_module_name)
            } in
          let uu____6145 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____6145 with
           | (vars,guards,env2,decls,uu____6160) ->
               let uu____6167 =
                 let uu____6174 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6199 =
                             let uu____6204 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6204 FStar_List.unzip in
                           match uu____6199 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6174 FStar_List.unzip in
               (match uu____6167 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6263 = env2 in
                      {
                        bindings = (uu___137_6263.bindings);
                        depth = (uu___137_6263.depth);
                        tcenv = (uu___137_6263.tcenv);
                        warn = (uu___137_6263.warn);
                        cache = (uu___137_6263.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6263.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6263.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6263.current_module_name)
                      } in
                    let uu____6264 =
                      let uu____6267 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6267 env3 in
                    (match uu____6264 with
                     | (pre1,decls'') ->
                         let uu____6272 =
                           let uu____6275 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6275 env3 in
                         (match uu____6272 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6282 =
                                let uu____6283 =
                                  let uu____6289 =
                                    let uu____6290 =
                                      let uu____6293 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6293, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6290 in
                                  (pats, vars, uu____6289) in
                                FStar_SMTEncoding_Util.mkForall uu____6283 in
                              (uu____6282, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6306 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6306
        then
          let uu____6307 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6308 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6307 uu____6308
        else () in
      let enc f r l =
        let uu____6335 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6353 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____6353 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6335 with
        | (decls,args) ->
            let uu____6370 =
              let uu___138_6371 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6371.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6371.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6370, decls) in
      let const_op f r uu____6395 = let uu____6403 = f r in (uu____6403, []) in
      let un_op f l =
        let uu____6419 = FStar_List.hd l in FStar_All.pipe_left f uu____6419 in
      let bin_op f uu___112_6432 =
        match uu___112_6432 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6440 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6467 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6483  ->
                 match uu____6483 with
                 | (t,uu____6491) ->
                     let uu____6492 = encode_formula t env in
                     (match uu____6492 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6467 with
        | (decls,phis) ->
            let uu____6509 =
              let uu___139_6510 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6510.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6510.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6509, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6549  ->
               match uu____6549 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____6560) -> false
                    | uu____6561 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6573 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6573
        else
          (let uu____6587 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6587 r rf) in
      let mk_imp1 r uu___113_6606 =
        match uu___113_6606 with
        | (lhs,uu____6610)::(rhs,uu____6612)::[] ->
            let uu____6626 = encode_formula rhs env in
            (match uu____6626 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6635) ->
                      (l1, decls1)
                  | uu____6638 ->
                      let uu____6639 = encode_formula lhs env in
                      (match uu____6639 with
                       | (l2,decls2) ->
                           let uu____6646 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6646, (FStar_List.append decls1 decls2)))))
        | uu____6648 -> failwith "impossible" in
      let mk_ite r uu___114_6663 =
        match uu___114_6663 with
        | (guard,uu____6667)::(_then,uu____6669)::(_else,uu____6671)::[] ->
            let uu____6690 = encode_formula guard env in
            (match uu____6690 with
             | (g,decls1) ->
                 let uu____6697 = encode_formula _then env in
                 (match uu____6697 with
                  | (t,decls2) ->
                      let uu____6704 = encode_formula _else env in
                      (match uu____6704 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6713 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6732 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6732 in
      let connectives =
        let uu____6744 =
          let uu____6753 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____6753) in
        let uu____6766 =
          let uu____6776 =
            let uu____6785 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____6785) in
          let uu____6798 =
            let uu____6808 =
              let uu____6818 =
                let uu____6827 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____6827) in
              let uu____6840 =
                let uu____6850 =
                  let uu____6860 =
                    let uu____6869 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____6869) in
                  [uu____6860;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____6850 in
              uu____6818 :: uu____6840 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____6808 in
          uu____6776 :: uu____6798 in
        uu____6744 :: uu____6766 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7072 = encode_formula phi' env in
            (match uu____7072 with
             | (phi2,decls) ->
                 let uu____7079 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7079, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7080 ->
            let uu____7084 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7084 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7105 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7105 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7113;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7115;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7127 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7127 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7154::(x,uu____7156)::(t,uu____7158)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____7182 = encode_term x env in
                 (match uu____7182 with
                  | (x1,decls) ->
                      let uu____7189 = encode_term t env in
                      (match uu____7189 with
                       | (t1,decls') ->
                           let uu____7196 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7196, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7200)::(msg,uu____7202)::(phi2,uu____7204)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____7227 =
                   let uu____7230 =
                     let uu____7231 = FStar_Syntax_Subst.compress r in
                     uu____7231.FStar_Syntax_Syntax.n in
                   let uu____7233 =
                     let uu____7234 = FStar_Syntax_Subst.compress msg in
                     uu____7234.FStar_Syntax_Syntax.n in
                   (uu____7230, uu____7233) in
                 (match uu____7227 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7240))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____7249 -> fallback phi2)
             | uu____7252 when head_redex env head2 ->
                 let uu____7259 = whnf env phi1 in
                 encode_formula uu____7259 env
             | uu____7260 ->
                 let uu____7267 = encode_term phi1 env in
                 (match uu____7267 with
                  | (tt,decls) ->
                      let uu____7274 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7277 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7277.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7277.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7274, decls)))
        | uu____7280 ->
            let uu____7281 = encode_term phi1 env in
            (match uu____7281 with
             | (tt,decls) ->
                 let uu____7288 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7291 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7291.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7291.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7288, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7318 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____7318 with
        | (vars,guards,env2,decls,uu____7340) ->
            let uu____7347 =
              let uu____7354 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7381 =
                          let uu____7386 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7403  ->
                                    match uu____7403 with
                                    | (t,uu____7409) ->
                                        encode_term t
                                          (let uu___142_7411 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7411.bindings);
                                             depth = (uu___142_7411.depth);
                                             tcenv = (uu___142_7411.tcenv);
                                             warn = (uu___142_7411.warn);
                                             cache = (uu___142_7411.cache);
                                             nolabels =
                                               (uu___142_7411.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7411.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7411.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7386 FStar_List.unzip in
                        match uu____7381 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7354 FStar_List.unzip in
            (match uu____7347 with
             | (pats,decls') ->
                 let uu____7463 = encode_formula body env2 in
                 (match uu____7463 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7482;
                             FStar_SMTEncoding_Term.rng = uu____7483;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____7491 -> guards in
                      let uu____7494 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7494, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7531  ->
                   match uu____7531 with
                   | (x,uu____7535) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7541 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7550 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7550) uu____7541 tl1 in
             let uu____7552 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7568  ->
                       match uu____7568 with
                       | (b,uu____7572) ->
                           let uu____7573 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7573)) in
             (match uu____7552 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____7577) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7587 =
                    let uu____7588 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7588 in
                  FStar_Errors.warn pos uu____7587) in
       let uu____7589 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7589 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____7595 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7634  ->
                     match uu____7634 with
                     | (l,uu____7644) -> FStar_Ident.lid_equals op l)) in
           (match uu____7595 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____7667,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7696 = encode_q_body env vars pats body in
             match uu____7696 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7722 =
                     let uu____7728 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7728) in
                   FStar_SMTEncoding_Term.mkForall uu____7722
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7740 = encode_q_body env vars pats body in
             match uu____7740 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7765 =
                   let uu____7766 =
                     let uu____7772 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7772) in
                   FStar_SMTEncoding_Term.mkExists uu____7766
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7765, decls))))
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
  let uu____7851 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7851 with
  | (asym,a) ->
      let uu____7856 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7856 with
       | (xsym,x) ->
           let uu____7861 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7861 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7891 =
                      let uu____7897 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____7897, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7891 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____7912 =
                      let uu____7916 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7916) in
                    FStar_SMTEncoding_Util.mkApp uu____7912 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7924 =
                    let uu____7926 =
                      let uu____7928 =
                        let uu____7930 =
                          let uu____7931 =
                            let uu____7935 =
                              let uu____7936 =
                                let uu____7942 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7942) in
                              FStar_SMTEncoding_Util.mkForall uu____7936 in
                            (uu____7935, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7931 in
                        let uu____7951 =
                          let uu____7953 =
                            let uu____7954 =
                              let uu____7958 =
                                let uu____7959 =
                                  let uu____7965 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7965) in
                                FStar_SMTEncoding_Util.mkForall uu____7959 in
                              (uu____7958,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7954 in
                          [uu____7953] in
                        uu____7930 :: uu____7951 in
                      xtok_decl :: uu____7928 in
                    xname_decl :: uu____7926 in
                  (xtok1, uu____7924) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8014 =
                    let uu____8022 =
                      let uu____8028 =
                        let uu____8029 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8029 in
                      quant axy uu____8028 in
                    (FStar_Parser_Const.op_Eq, uu____8022) in
                  let uu____8035 =
                    let uu____8044 =
                      let uu____8052 =
                        let uu____8058 =
                          let uu____8059 =
                            let uu____8060 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8060 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8059 in
                        quant axy uu____8058 in
                      (FStar_Parser_Const.op_notEq, uu____8052) in
                    let uu____8066 =
                      let uu____8075 =
                        let uu____8083 =
                          let uu____8089 =
                            let uu____8090 =
                              let uu____8091 =
                                let uu____8094 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8095 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8094, uu____8095) in
                              FStar_SMTEncoding_Util.mkLT uu____8091 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8090 in
                          quant xy uu____8089 in
                        (FStar_Parser_Const.op_LT, uu____8083) in
                      let uu____8101 =
                        let uu____8110 =
                          let uu____8118 =
                            let uu____8124 =
                              let uu____8125 =
                                let uu____8126 =
                                  let uu____8129 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8130 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8129, uu____8130) in
                                FStar_SMTEncoding_Util.mkLTE uu____8126 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8125 in
                            quant xy uu____8124 in
                          (FStar_Parser_Const.op_LTE, uu____8118) in
                        let uu____8136 =
                          let uu____8145 =
                            let uu____8153 =
                              let uu____8159 =
                                let uu____8160 =
                                  let uu____8161 =
                                    let uu____8164 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8165 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8164, uu____8165) in
                                  FStar_SMTEncoding_Util.mkGT uu____8161 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8160 in
                              quant xy uu____8159 in
                            (FStar_Parser_Const.op_GT, uu____8153) in
                          let uu____8171 =
                            let uu____8180 =
                              let uu____8188 =
                                let uu____8194 =
                                  let uu____8195 =
                                    let uu____8196 =
                                      let uu____8199 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8200 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8199, uu____8200) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8196 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8195 in
                                quant xy uu____8194 in
                              (FStar_Parser_Const.op_GTE, uu____8188) in
                            let uu____8206 =
                              let uu____8215 =
                                let uu____8223 =
                                  let uu____8229 =
                                    let uu____8230 =
                                      let uu____8231 =
                                        let uu____8234 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8235 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8234, uu____8235) in
                                      FStar_SMTEncoding_Util.mkSub uu____8231 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8230 in
                                  quant xy uu____8229 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____8223) in
                              let uu____8241 =
                                let uu____8250 =
                                  let uu____8258 =
                                    let uu____8264 =
                                      let uu____8265 =
                                        let uu____8266 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8266 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8265 in
                                    quant qx uu____8264 in
                                  (FStar_Parser_Const.op_Minus, uu____8258) in
                                let uu____8272 =
                                  let uu____8281 =
                                    let uu____8289 =
                                      let uu____8295 =
                                        let uu____8296 =
                                          let uu____8297 =
                                            let uu____8300 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8301 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8300, uu____8301) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8297 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8296 in
                                      quant xy uu____8295 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____8289) in
                                  let uu____8307 =
                                    let uu____8316 =
                                      let uu____8324 =
                                        let uu____8330 =
                                          let uu____8331 =
                                            let uu____8332 =
                                              let uu____8335 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8336 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8335, uu____8336) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8332 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8331 in
                                        quant xy uu____8330 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____8324) in
                                    let uu____8342 =
                                      let uu____8351 =
                                        let uu____8359 =
                                          let uu____8365 =
                                            let uu____8366 =
                                              let uu____8367 =
                                                let uu____8370 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8371 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8370, uu____8371) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8367 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8366 in
                                          quant xy uu____8365 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____8359) in
                                      let uu____8377 =
                                        let uu____8386 =
                                          let uu____8394 =
                                            let uu____8400 =
                                              let uu____8401 =
                                                let uu____8402 =
                                                  let uu____8405 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8406 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8405, uu____8406) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8402 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8401 in
                                            quant xy uu____8400 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____8394) in
                                        let uu____8412 =
                                          let uu____8421 =
                                            let uu____8429 =
                                              let uu____8435 =
                                                let uu____8436 =
                                                  let uu____8437 =
                                                    let uu____8440 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8441 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8440, uu____8441) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8437 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8436 in
                                              quant xy uu____8435 in
                                            (FStar_Parser_Const.op_And,
                                              uu____8429) in
                                          let uu____8447 =
                                            let uu____8456 =
                                              let uu____8464 =
                                                let uu____8470 =
                                                  let uu____8471 =
                                                    let uu____8472 =
                                                      let uu____8475 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8476 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8475,
                                                        uu____8476) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8472 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8471 in
                                                quant xy uu____8470 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____8464) in
                                            let uu____8482 =
                                              let uu____8491 =
                                                let uu____8499 =
                                                  let uu____8505 =
                                                    let uu____8506 =
                                                      let uu____8507 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8507 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8506 in
                                                  quant qx uu____8505 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____8499) in
                                              [uu____8491] in
                                            uu____8456 :: uu____8482 in
                                          uu____8421 :: uu____8447 in
                                        uu____8386 :: uu____8412 in
                                      uu____8351 :: uu____8377 in
                                    uu____8316 :: uu____8342 in
                                  uu____8281 :: uu____8307 in
                                uu____8250 :: uu____8272 in
                              uu____8215 :: uu____8241 in
                            uu____8180 :: uu____8206 in
                          uu____8145 :: uu____8171 in
                        uu____8110 :: uu____8136 in
                      uu____8075 :: uu____8101 in
                    uu____8044 :: uu____8066 in
                  uu____8014 :: uu____8035 in
                let mk1 l v1 =
                  let uu____8635 =
                    let uu____8640 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8675  ->
                              match uu____8675 with
                              | (l',uu____8684) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8640
                      (FStar_Option.map
                         (fun uu____8720  ->
                            match uu____8720 with | (uu____8731,b) -> b v1)) in
                  FStar_All.pipe_right uu____8635 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8775  ->
                          match uu____8775 with
                          | (l',uu____8784) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8813 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8813 with
        | (xxsym,xx) ->
            let uu____8818 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8818 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8826 =
                   let uu____8830 =
                     let uu____8831 =
                       let uu____8837 =
                         let uu____8838 =
                           let uu____8841 =
                             let uu____8842 =
                               let uu____8845 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8845) in
                             FStar_SMTEncoding_Util.mkEq uu____8842 in
                           (xx_has_type, uu____8841) in
                         FStar_SMTEncoding_Util.mkImp uu____8838 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8837) in
                     FStar_SMTEncoding_Util.mkForall uu____8831 in
                   let uu____8858 =
                     let uu____8859 =
                       let uu____8860 =
                         let uu____8861 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8861 in
                       Prims.strcat module_name uu____8860 in
                     varops.mk_unique uu____8859 in
                   (uu____8830, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____8858) in
                 FStar_SMTEncoding_Util.mkAssume uu____8826)
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
    let uu____8895 =
      let uu____8896 =
        let uu____8900 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8900, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8896 in
    let uu____8902 =
      let uu____8904 =
        let uu____8905 =
          let uu____8909 =
            let uu____8910 =
              let uu____8916 =
                let uu____8917 =
                  let uu____8920 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8920) in
                FStar_SMTEncoding_Util.mkImp uu____8917 in
              ([[typing_pred]], [xx], uu____8916) in
            mkForall_fuel uu____8910 in
          (uu____8909, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8905 in
      [uu____8904] in
    uu____8895 :: uu____8902 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8948 =
      let uu____8949 =
        let uu____8953 =
          let uu____8954 =
            let uu____8960 =
              let uu____8963 =
                let uu____8965 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8965] in
              [uu____8963] in
            let uu____8968 =
              let uu____8969 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8969 tt in
            (uu____8960, [bb], uu____8968) in
          FStar_SMTEncoding_Util.mkForall uu____8954 in
        (uu____8953, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8949 in
    let uu____8980 =
      let uu____8982 =
        let uu____8983 =
          let uu____8987 =
            let uu____8988 =
              let uu____8994 =
                let uu____8995 =
                  let uu____8998 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8998) in
                FStar_SMTEncoding_Util.mkImp uu____8995 in
              ([[typing_pred]], [xx], uu____8994) in
            mkForall_fuel uu____8988 in
          (uu____8987, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8983 in
      [uu____8982] in
    uu____8948 :: uu____8980 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9032 =
        let uu____9033 =
          let uu____9037 =
            let uu____9039 =
              let uu____9041 =
                let uu____9043 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9044 =
                  let uu____9046 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9046] in
                uu____9043 :: uu____9044 in
              tt :: uu____9041 in
            tt :: uu____9039 in
          ("Prims.Precedes", uu____9037) in
        FStar_SMTEncoding_Util.mkApp uu____9033 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9032 in
    let precedes_y_x =
      let uu____9049 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9049 in
    let uu____9051 =
      let uu____9052 =
        let uu____9056 =
          let uu____9057 =
            let uu____9063 =
              let uu____9066 =
                let uu____9068 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9068] in
              [uu____9066] in
            let uu____9071 =
              let uu____9072 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9072 tt in
            (uu____9063, [bb], uu____9071) in
          FStar_SMTEncoding_Util.mkForall uu____9057 in
        (uu____9056, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9052 in
    let uu____9083 =
      let uu____9085 =
        let uu____9086 =
          let uu____9090 =
            let uu____9091 =
              let uu____9097 =
                let uu____9098 =
                  let uu____9101 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9101) in
                FStar_SMTEncoding_Util.mkImp uu____9098 in
              ([[typing_pred]], [xx], uu____9097) in
            mkForall_fuel uu____9091 in
          (uu____9090, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9086 in
      let uu____9114 =
        let uu____9116 =
          let uu____9117 =
            let uu____9121 =
              let uu____9122 =
                let uu____9128 =
                  let uu____9129 =
                    let uu____9132 =
                      let uu____9133 =
                        let uu____9135 =
                          let uu____9137 =
                            let uu____9139 =
                              let uu____9140 =
                                let uu____9143 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9144 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9143, uu____9144) in
                              FStar_SMTEncoding_Util.mkGT uu____9140 in
                            let uu____9145 =
                              let uu____9147 =
                                let uu____9148 =
                                  let uu____9151 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9152 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9151, uu____9152) in
                                FStar_SMTEncoding_Util.mkGTE uu____9148 in
                              let uu____9153 =
                                let uu____9155 =
                                  let uu____9156 =
                                    let uu____9159 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9160 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9159, uu____9160) in
                                  FStar_SMTEncoding_Util.mkLT uu____9156 in
                                [uu____9155] in
                              uu____9147 :: uu____9153 in
                            uu____9139 :: uu____9145 in
                          typing_pred_y :: uu____9137 in
                        typing_pred :: uu____9135 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9133 in
                    (uu____9132, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9129 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9128) in
              mkForall_fuel uu____9122 in
            (uu____9121,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9117 in
        [uu____9116] in
      uu____9085 :: uu____9114 in
    uu____9051 :: uu____9083 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9190 =
      let uu____9191 =
        let uu____9195 =
          let uu____9196 =
            let uu____9202 =
              let uu____9205 =
                let uu____9207 = FStar_SMTEncoding_Term.boxString b in
                [uu____9207] in
              [uu____9205] in
            let uu____9210 =
              let uu____9211 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9211 tt in
            (uu____9202, [bb], uu____9210) in
          FStar_SMTEncoding_Util.mkForall uu____9196 in
        (uu____9195, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9191 in
    let uu____9222 =
      let uu____9224 =
        let uu____9225 =
          let uu____9229 =
            let uu____9230 =
              let uu____9236 =
                let uu____9237 =
                  let uu____9240 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9240) in
                FStar_SMTEncoding_Util.mkImp uu____9237 in
              ([[typing_pred]], [xx], uu____9236) in
            mkForall_fuel uu____9230 in
          (uu____9229, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9225 in
      [uu____9224] in
    uu____9190 :: uu____9222 in
  let mk_ref1 env reft_name uu____9262 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9273 =
        let uu____9277 =
          let uu____9279 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9279] in
        (reft_name, uu____9277) in
      FStar_SMTEncoding_Util.mkApp uu____9273 in
    let refb =
      let uu____9282 =
        let uu____9286 =
          let uu____9288 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9288] in
        (reft_name, uu____9286) in
      FStar_SMTEncoding_Util.mkApp uu____9282 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9292 =
      let uu____9293 =
        let uu____9297 =
          let uu____9298 =
            let uu____9304 =
              let uu____9305 =
                let uu____9308 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9308) in
              FStar_SMTEncoding_Util.mkImp uu____9305 in
            ([[typing_pred]], [xx; aa], uu____9304) in
          mkForall_fuel uu____9298 in
        (uu____9297, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9293 in
    [uu____9292] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9348 =
      let uu____9349 =
        let uu____9353 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9353, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9349 in
    [uu____9348] in
  let mk_and_interp env conj uu____9364 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9381 =
      let uu____9382 =
        let uu____9386 =
          let uu____9387 =
            let uu____9393 =
              let uu____9394 =
                let uu____9397 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9397, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9394 in
            ([[l_and_a_b]], [aa; bb], uu____9393) in
          FStar_SMTEncoding_Util.mkForall uu____9387 in
        (uu____9386, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9382 in
    [uu____9381] in
  let mk_or_interp env disj uu____9421 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9438 =
      let uu____9439 =
        let uu____9443 =
          let uu____9444 =
            let uu____9450 =
              let uu____9451 =
                let uu____9454 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9454, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9451 in
            ([[l_or_a_b]], [aa; bb], uu____9450) in
          FStar_SMTEncoding_Util.mkForall uu____9444 in
        (uu____9443, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9439 in
    [uu____9438] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9495 =
      let uu____9496 =
        let uu____9500 =
          let uu____9501 =
            let uu____9507 =
              let uu____9508 =
                let uu____9511 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9511, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9508 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9507) in
          FStar_SMTEncoding_Util.mkForall uu____9501 in
        (uu____9500, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9496 in
    [uu____9495] in
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
    let uu____9558 =
      let uu____9559 =
        let uu____9563 =
          let uu____9564 =
            let uu____9570 =
              let uu____9571 =
                let uu____9574 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9574, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9571 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9570) in
          FStar_SMTEncoding_Util.mkForall uu____9564 in
        (uu____9563, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9559 in
    [uu____9558] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9619 =
      let uu____9620 =
        let uu____9624 =
          let uu____9625 =
            let uu____9631 =
              let uu____9632 =
                let uu____9635 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9635, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9632 in
            ([[l_imp_a_b]], [aa; bb], uu____9631) in
          FStar_SMTEncoding_Util.mkForall uu____9625 in
        (uu____9624, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9620 in
    [uu____9619] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9676 =
      let uu____9677 =
        let uu____9681 =
          let uu____9682 =
            let uu____9688 =
              let uu____9689 =
                let uu____9692 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9692, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9689 in
            ([[l_iff_a_b]], [aa; bb], uu____9688) in
          FStar_SMTEncoding_Util.mkForall uu____9682 in
        (uu____9681, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9677 in
    [uu____9676] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9726 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9726 in
    let uu____9728 =
      let uu____9729 =
        let uu____9733 =
          let uu____9734 =
            let uu____9740 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9740) in
          FStar_SMTEncoding_Util.mkForall uu____9734 in
        (uu____9733, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9729 in
    [uu____9728] in
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
      let uu____9780 =
        let uu____9784 =
          let uu____9786 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9786] in
        ("Valid", uu____9784) in
      FStar_SMTEncoding_Util.mkApp uu____9780 in
    let uu____9788 =
      let uu____9789 =
        let uu____9793 =
          let uu____9794 =
            let uu____9800 =
              let uu____9801 =
                let uu____9804 =
                  let uu____9805 =
                    let uu____9811 =
                      let uu____9814 =
                        let uu____9816 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9816] in
                      [uu____9814] in
                    let uu____9819 =
                      let uu____9820 =
                        let uu____9823 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9823, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9820 in
                    (uu____9811, [xx1], uu____9819) in
                  FStar_SMTEncoding_Util.mkForall uu____9805 in
                (uu____9804, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9801 in
            ([[l_forall_a_b]], [aa; bb], uu____9800) in
          FStar_SMTEncoding_Util.mkForall uu____9794 in
        (uu____9793, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9789 in
    [uu____9788] in
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
      let uu____9874 =
        let uu____9878 =
          let uu____9880 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9880] in
        ("Valid", uu____9878) in
      FStar_SMTEncoding_Util.mkApp uu____9874 in
    let uu____9882 =
      let uu____9883 =
        let uu____9887 =
          let uu____9888 =
            let uu____9894 =
              let uu____9895 =
                let uu____9898 =
                  let uu____9899 =
                    let uu____9905 =
                      let uu____9908 =
                        let uu____9910 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9910] in
                      [uu____9908] in
                    let uu____9913 =
                      let uu____9914 =
                        let uu____9917 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9917, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9914 in
                    (uu____9905, [xx1], uu____9913) in
                  FStar_SMTEncoding_Util.mkExists uu____9899 in
                (uu____9898, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9895 in
            ([[l_exists_a_b]], [aa; bb], uu____9894) in
          FStar_SMTEncoding_Util.mkForall uu____9888 in
        (uu____9887, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9883 in
    [uu____9882] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9953 =
      let uu____9954 =
        let uu____9958 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9959 = varops.mk_unique "typing_range_const" in
        (uu____9958, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____9959) in
      FStar_SMTEncoding_Util.mkAssume uu____9954 in
    [uu____9953] in
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
          let uu____10221 =
            FStar_Util.find_opt
              (fun uu____10242  ->
                 match uu____10242 with
                 | (l,uu____10252) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10221 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____10274,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10310 = encode_function_type_as_formula t env in
        match uu____10310 with
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
            let uu____10343 =
              (let uu____10346 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10346) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10343
            then
              let uu____10350 = new_term_constant_and_tok_from_lid env lid in
              match uu____10350 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10362 =
                      let uu____10363 = FStar_Syntax_Subst.compress t_norm in
                      uu____10363.FStar_Syntax_Syntax.n in
                    match uu____10362 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10367) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10383  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10386 -> [] in
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
              (let uu____10395 = prims.is lid in
               if uu____10395
               then
                 let vname = varops.new_fvar lid in
                 let uu____10400 = prims.mk lid vname in
                 match uu____10400 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10415 =
                    let uu____10421 = curried_arrow_formals_comp t_norm in
                    match uu____10421 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10432 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10432
                          then
                            let uu____10433 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10436 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10436.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10436.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10436.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10436.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10436.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10436.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10436.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10436.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10436.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10436.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10436.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10436.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10436.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10436.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10436.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10436.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10436.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10436.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10436.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10436.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10436.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10436.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10436.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10436.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10436.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10436.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10433
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10443 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10443)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10415 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10468 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10468 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10481 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10513  ->
                                     match uu___115_10513 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10516 =
                                           FStar_Util.prefix vars in
                                         (match uu____10516 with
                                          | (uu____10527,(xxsym,uu____10529))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10539 =
                                                let uu____10540 =
                                                  let uu____10544 =
                                                    let uu____10545 =
                                                      let uu____10551 =
                                                        let uu____10552 =
                                                          let uu____10555 =
                                                            let uu____10556 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10556 in
                                                          (vapp, uu____10555) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10552 in
                                                      ([[vapp]], vars,
                                                        uu____10551) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10545 in
                                                  (uu____10544,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10540 in
                                              [uu____10539])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10567 =
                                           FStar_Util.prefix vars in
                                         (match uu____10567 with
                                          | (uu____10578,(xxsym,uu____10580))
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
                                              let uu____10594 =
                                                let uu____10595 =
                                                  let uu____10599 =
                                                    let uu____10600 =
                                                      let uu____10606 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10606) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10600 in
                                                  (uu____10599,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10595 in
                                              [uu____10594])
                                     | uu____10615 -> [])) in
                           let uu____10616 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____10616 with
                            | (vars,guards,env',decls1,uu____10632) ->
                                let uu____10639 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____10644 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10644, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____10646 = encode_formula p env' in
                                      (match uu____10646 with
                                       | (g,ds) ->
                                           let uu____10653 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10653,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10639 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10662 =
                                         let uu____10666 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10666) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10662 in
                                     let uu____10671 =
                                       let vname_decl =
                                         let uu____10676 =
                                           let uu____10682 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10688  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10682,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10676 in
                                       let uu____10693 =
                                         let env2 =
                                           let uu___144_10697 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10697.bindings);
                                             depth = (uu___144_10697.depth);
                                             tcenv = (uu___144_10697.tcenv);
                                             warn = (uu___144_10697.warn);
                                             cache = (uu___144_10697.cache);
                                             nolabels =
                                               (uu___144_10697.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10697.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10697.current_module_name)
                                           } in
                                         let uu____10698 =
                                           let uu____10699 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10699 in
                                         if uu____10698
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____10693 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10709::uu____10710 ->
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
                                                   let uu____10733 =
                                                     let uu____10739 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10739) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10733 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10753 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10755 =
                                             match formals with
                                             | [] ->
                                                 let uu____10764 =
                                                   let uu____10765 =
                                                     let uu____10767 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____10767 in
                                                   push_free_var env1 lid
                                                     vname uu____10765 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10764)
                                             | uu____10770 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____10775 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10775 in
                                                 let name_tok_corr =
                                                   let uu____10777 =
                                                     let uu____10781 =
                                                       let uu____10782 =
                                                         let uu____10788 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10788) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10782 in
                                                     (uu____10781,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10777 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10755 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10671 with
                                      | (decls2,env2) ->
                                          let uu____10812 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10817 =
                                              encode_term res_t1 env' in
                                            match uu____10817 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10825 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10825,
                                                  decls) in
                                          (match uu____10812 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10833 =
                                                   let uu____10837 =
                                                     let uu____10838 =
                                                       let uu____10844 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10844) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10838 in
                                                   (uu____10837,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10833 in
                                               let freshness =
                                                 let uu____10853 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10853
                                                 then
                                                   let uu____10856 =
                                                     let uu____10857 =
                                                       let uu____10863 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____10869 =
                                                         varops.next_id () in
                                                       (vname, uu____10863,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10869) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10857 in
                                                   let uu____10871 =
                                                     let uu____10873 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10873] in
                                                   uu____10856 :: uu____10871
                                                 else [] in
                                               let g =
                                                 let uu____10877 =
                                                   let uu____10879 =
                                                     let uu____10881 =
                                                       let uu____10883 =
                                                         let uu____10885 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10885 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10883 in
                                                     FStar_List.append decls3
                                                       uu____10881 in
                                                   FStar_List.append decls2
                                                     uu____10879 in
                                                 FStar_List.append decls11
                                                   uu____10877 in
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
          let uu____10911 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10911 with
          | FStar_Pervasives_Native.None  ->
              let uu____10930 = encode_free_var env x t t_norm [] in
              (match uu____10930 with
               | (decls,env1) ->
                   let uu____10945 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10945 with
                    | (n1,x',uu____10960) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____10972) ->
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
          let uu____11009 = encode_free_var env lid t tt quals in
          match uu____11009 with
          | (decls,env1) ->
              let uu____11020 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11020
              then
                let uu____11024 =
                  let uu____11026 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11026 in
                (uu____11024, env1)
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
             (fun uu____11064  ->
                fun lb  ->
                  match uu____11064 with
                  | (decls,env1) ->
                      let uu____11076 =
                        let uu____11080 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11080
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11076 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11095 = FStar_Syntax_Util.head_and_args t in
    match uu____11095 with
    | (hd1,args) ->
        let uu____11115 =
          let uu____11116 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11116.FStar_Syntax_Syntax.n in
        (match uu____11115 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11119,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11130 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____11148  ->
      fun quals  ->
        match uu____11148 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11197 = FStar_Util.first_N nbinders formals in
              match uu____11197 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11245  ->
                         fun uu____11246  ->
                           match (uu____11245, uu____11246) with
                           | ((formal,uu____11256),(binder,uu____11258)) ->
                               let uu____11263 =
                                 let uu____11267 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11267) in
                               FStar_Syntax_Syntax.NT uu____11263) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11272 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11290  ->
                              match uu____11290 with
                              | (x,i) ->
                                  let uu____11297 =
                                    let uu___145_11298 = x in
                                    let uu____11299 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11298.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11298.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11299
                                    } in
                                  (uu____11297, i))) in
                    FStar_All.pipe_right uu____11272
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11309 =
                      let uu____11310 = FStar_Syntax_Subst.compress body in
                      let uu____11311 =
                        let uu____11312 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____11312 in
                      FStar_Syntax_Syntax.extend_app_n uu____11310
                        uu____11311 in
                    uu____11309 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11353 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11353
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11356 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11356.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11356.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11356.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11356.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11356.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11356.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11356.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11356.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11356.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11356.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11356.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11356.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11356.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11356.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11356.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11356.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11356.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11356.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11356.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11356.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11356.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11356.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11356.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11356.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11356.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11356.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11377 = FStar_Syntax_Util.abs_formals e in
                match uu____11377 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11411::uu____11412 ->
                         let uu____11420 =
                           let uu____11421 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11421.FStar_Syntax_Syntax.n in
                         (match uu____11420 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11445 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11445 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11473 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11473
                                   then
                                     let uu____11496 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11496 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11551  ->
                                                   fun uu____11552  ->
                                                     match (uu____11551,
                                                             uu____11552)
                                                     with
                                                     | ((x,uu____11562),
                                                        (b,uu____11564)) ->
                                                         let uu____11569 =
                                                           let uu____11573 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11573) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11569)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11575 =
                                            let uu____11586 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11586) in
                                          (uu____11575, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11626 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11626 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11673) ->
                              let uu____11676 =
                                let uu____11687 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____11687 in
                              (uu____11676, true)
                          | uu____11720 when Prims.op_Negation norm1 ->
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
                          | uu____11722 ->
                              let uu____11723 =
                                let uu____11724 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11725 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11724
                                  uu____11725 in
                              failwith uu____11723)
                     | uu____11738 ->
                         let uu____11739 =
                           let uu____11740 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11740.FStar_Syntax_Syntax.n in
                         (match uu____11739 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11764 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11764 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11782 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11782 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11825 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11855 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11855
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11863 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11917  ->
                            fun lb  ->
                              match uu____11917 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11968 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11968
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11971 =
                                      let uu____11979 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11979
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11971 with
                                    | (tok,decl,env2) ->
                                        let uu____12004 =
                                          let uu____12011 =
                                            let uu____12017 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12017, tok) in
                                          uu____12011 :: toks in
                                        (uu____12004, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11863 with
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
                        | uu____12119 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____12124 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12124 vars)
                            else
                              (let uu____12126 =
                                 let uu____12130 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12130) in
                               FStar_SMTEncoding_Util.mkApp uu____12126) in
                      let uu____12135 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_12138  ->
                                 match uu___116_12138 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12139 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12144 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12144))) in
                      if uu____12135
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12164;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12166;
                                FStar_Syntax_Syntax.lbeff = uu____12167;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12202 =
                                 let uu____12206 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12206 with
                                 | (tcenv',uu____12216,e_t) ->
                                     let uu____12220 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12227 -> failwith "Impossible" in
                                     (match uu____12220 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12237 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12237.bindings);
                                              depth = (uu___149_12237.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12237.warn);
                                              cache = (uu___149_12237.cache);
                                              nolabels =
                                                (uu___149_12237.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12237.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12237.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12237.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12202 with
                                | (env',e1,t_norm1) ->
                                    let uu____12244 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12244 with
                                     | ((binders,body,uu____12256,uu____12257),curry)
                                         ->
                                         ((let uu____12264 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12264
                                           then
                                             let uu____12265 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12266 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12265 uu____12266
                                           else ());
                                          (let uu____12268 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____12268 with
                                           | (vars,guards,env'1,binder_decls,uu____12284)
                                               ->
                                               let body1 =
                                                 let uu____12292 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12292
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12295 =
                                                 let uu____12300 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12300
                                                 then
                                                   let uu____12306 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12307 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12306, uu____12307)
                                                 else
                                                   (let uu____12313 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12313)) in
                                               (match uu____12295 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12327 =
                                                        let uu____12331 =
                                                          let uu____12332 =
                                                            let uu____12338 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12338) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12332 in
                                                        let uu____12344 =
                                                          let uu____12346 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____12346 in
                                                        (uu____12331,
                                                          uu____12344,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12327 in
                                                    let uu____12348 =
                                                      let uu____12350 =
                                                        let uu____12352 =
                                                          let uu____12354 =
                                                            let uu____12356 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12356 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12354 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12352 in
                                                      FStar_List.append
                                                        decls1 uu____12350 in
                                                    (uu____12348, env1))))))
                           | uu____12359 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12378 = varops.fresh "fuel" in
                             (uu____12378, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12381 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12431  ->
                                     fun uu____12432  ->
                                       match (uu____12431, uu____12432) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12510 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12510 in
                                           let gtok =
                                             let uu____12512 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12512 in
                                           let env3 =
                                             let uu____12514 =
                                               let uu____12516 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_42  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_42) uu____12516 in
                                             push_free_var env2 flid gtok
                                               uu____12514 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12381 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12601
                                 t_norm uu____12603 =
                                 match (uu____12601, uu____12603) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12629;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12630;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12645 =
                                       let uu____12649 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12649 with
                                       | (tcenv',uu____12661,e_t) ->
                                           let uu____12665 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12672 ->
                                                 failwith "Impossible" in
                                           (match uu____12665 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12682 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12682.bindings);
                                                    depth =
                                                      (uu___150_12682.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12682.warn);
                                                    cache =
                                                      (uu___150_12682.cache);
                                                    nolabels =
                                                      (uu___150_12682.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12682.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12682.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12682.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12645 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12692 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12692
                                            then
                                              let uu____12693 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12694 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12695 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12693 uu____12694
                                                uu____12695
                                            else ());
                                           (let uu____12697 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12697 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12719 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12719
                                                  then
                                                    let uu____12720 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12721 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12722 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12723 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12720 uu____12721
                                                      uu____12722 uu____12723
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12727 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____12727 with
                                                  | (vars,guards,env'1,binder_decls,uu____12745)
                                                      ->
                                                      let decl_g =
                                                        let uu____12753 =
                                                          let uu____12759 =
                                                            let uu____12761 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12761 in
                                                          (g, uu____12759,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12753 in
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
                                                        let uu____12776 =
                                                          let uu____12780 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12780) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12776 in
                                                      let gsapp =
                                                        let uu____12786 =
                                                          let uu____12790 =
                                                            let uu____12792 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12792 ::
                                                              vars_tm in
                                                          (g, uu____12790) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12786 in
                                                      let gmax =
                                                        let uu____12796 =
                                                          let uu____12800 =
                                                            let uu____12802 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12802 ::
                                                              vars_tm in
                                                          (g, uu____12800) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12796 in
                                                      let body1 =
                                                        let uu____12806 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12806
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12808 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12808 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12819
                                                               =
                                                               let uu____12823
                                                                 =
                                                                 let uu____12824
                                                                   =
                                                                   let uu____12832
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
                                                                    uu____12832) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12824 in
                                                               let uu____12843
                                                                 =
                                                                 let uu____12845
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____12845 in
                                                               (uu____12823,
                                                                 uu____12843,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12819 in
                                                           let eqn_f =
                                                             let uu____12848
                                                               =
                                                               let uu____12852
                                                                 =
                                                                 let uu____12853
                                                                   =
                                                                   let uu____12859
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12859) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12853 in
                                                               (uu____12852,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12848 in
                                                           let eqn_g' =
                                                             let uu____12867
                                                               =
                                                               let uu____12871
                                                                 =
                                                                 let uu____12872
                                                                   =
                                                                   let uu____12878
                                                                    =
                                                                    let uu____12879
                                                                    =
                                                                    let uu____12882
                                                                    =
                                                                    let uu____12883
                                                                    =
                                                                    let uu____12887
                                                                    =
                                                                    let uu____12889
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12889
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12887) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12883 in
                                                                    (gsapp,
                                                                    uu____12882) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12879 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12878) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12872 in
                                                               (uu____12871,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12867 in
                                                           let uu____12901 =
                                                             let uu____12906
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____12906
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12923)
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
                                                                    let uu____12938
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12938
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12941
                                                                    =
                                                                    let uu____12945
                                                                    =
                                                                    let uu____12946
                                                                    =
                                                                    let uu____12952
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12952) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12946 in
                                                                    (uu____12945,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12941 in
                                                                 let uu____12963
                                                                   =
                                                                   let uu____12967
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____12967
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12975
                                                                    =
                                                                    let uu____12977
                                                                    =
                                                                    let uu____12978
                                                                    =
                                                                    let uu____12982
                                                                    =
                                                                    let uu____12983
                                                                    =
                                                                    let uu____12989
                                                                    =
                                                                    let uu____12990
                                                                    =
                                                                    let uu____12993
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12993,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12990 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12989) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12983 in
                                                                    (uu____12982,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12978 in
                                                                    [uu____12977] in
                                                                    (d3,
                                                                    uu____12975) in
                                                                 (match uu____12963
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12901
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
                               let uu____13028 =
                                 let uu____13035 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13081  ->
                                      fun uu____13082  ->
                                        match (uu____13081, uu____13082) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13163 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13163 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13035 in
                               (match uu____13028 with
                                | (decls2,eqns,env01) ->
                                    let uu____13203 =
                                      let isDeclFun uu___117_13211 =
                                        match uu___117_13211 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13212 -> true
                                        | uu____13218 -> false in
                                      let uu____13219 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13219
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13203 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13249 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13249
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
        let uu____13283 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13283 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____13286 = encode_sigelt' env se in
      match uu____13286 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13296 =
                  let uu____13297 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13297 in
                [uu____13296]
            | uu____13298 ->
                let uu____13299 =
                  let uu____13301 =
                    let uu____13302 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13302 in
                  uu____13301 :: g in
                let uu____13303 =
                  let uu____13305 =
                    let uu____13306 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13306 in
                  [uu____13305] in
                FStar_List.append uu____13299 uu____13303 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13316 =
          let uu____13317 = FStar_Syntax_Subst.compress t in
          uu____13317.FStar_Syntax_Syntax.n in
        match uu____13316 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13320)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13323 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13326 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13329 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13331 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13333 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13341 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13344 =
            let uu____13345 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13345 Prims.op_Negation in
          if uu____13344
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13361 ->
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
               let uu____13378 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13378 with
               | (aname,atok,env2) ->
                   let uu____13388 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13388 with
                    | (formals,uu____13398) ->
                        let uu____13405 =
                          let uu____13408 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13408 env2 in
                        (match uu____13405 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13416 =
                                 let uu____13417 =
                                   let uu____13423 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13432  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13423,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13417 in
                               [uu____13416;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____13439 =
                               let aux uu____13468 uu____13469 =
                                 match (uu____13468, uu____13469) with
                                 | ((bv,uu____13496),(env3,acc_sorts,acc)) ->
                                     let uu____13517 = gen_term_var env3 bv in
                                     (match uu____13517 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13439 with
                              | (uu____13555,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13569 =
                                      let uu____13573 =
                                        let uu____13574 =
                                          let uu____13580 =
                                            let uu____13581 =
                                              let uu____13584 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13584) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13581 in
                                          ([[app]], xs_sorts, uu____13580) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13574 in
                                      (uu____13573,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13569 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13596 =
                                      let uu____13600 =
                                        let uu____13601 =
                                          let uu____13607 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13607) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13601 in
                                      (uu____13600,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13596 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13617 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13617 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13633,uu____13634)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____13635 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13635 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13646,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13651 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13654  ->
                      match uu___118_13654 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13655 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13658 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13659 -> false)) in
            Prims.op_Negation uu____13651 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____13665 = encode_top_level_val env fv t quals in
             match uu____13665 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13677 =
                   let uu____13679 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13679 in
                 (uu____13677, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____13685 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____13685 with
           | (uu____13690,f1) ->
               let uu____13692 = encode_formula f1 env in
               (match uu____13692 with
                | (f2,decls) ->
                    let g =
                      let uu____13701 =
                        let uu____13702 =
                          let uu____13706 =
                            let uu____13708 =
                              let uu____13709 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____13709 in
                            FStar_Pervasives_Native.Some uu____13708 in
                          let uu____13710 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____13706, uu____13710) in
                        FStar_SMTEncoding_Util.mkAssume uu____13702 in
                      [uu____13701] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13714) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____13721 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13736 =
                       let uu____13738 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13738.FStar_Syntax_Syntax.fv_name in
                     uu____13736.FStar_Syntax_Syntax.v in
                   let uu____13739 =
                     let uu____13740 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13740 in
                   if uu____13739
                   then
                     let val_decl =
                       let uu___151_13755 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13755.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13755.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_13755.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____13758 = encode_sigelt' env1 val_decl in
                     match uu____13758 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____13721 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13775,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13777;
                          FStar_Syntax_Syntax.lbtyp = uu____13778;
                          FStar_Syntax_Syntax.lbeff = uu____13779;
                          FStar_Syntax_Syntax.lbdef = uu____13780;_}::[]),uu____13781)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____13791 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13791 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13810 =
                   let uu____13812 =
                     let uu____13813 =
                       let uu____13817 =
                         let uu____13818 =
                           let uu____13824 =
                             let uu____13825 =
                               let uu____13828 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13828) in
                             FStar_SMTEncoding_Util.mkEq uu____13825 in
                           ([[b2t_x]], [xx], uu____13824) in
                         FStar_SMTEncoding_Util.mkForall uu____13818 in
                       (uu____13817,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13813 in
                   [uu____13812] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____13810 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13845,uu____13846) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13852  ->
                  match uu___119_13852 with
                  | FStar_Syntax_Syntax.Discriminator uu____13853 -> true
                  | uu____13854 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13856,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13864 =
                     let uu____13865 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13865.FStar_Ident.idText in
                   uu____13864 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13868  ->
                     match uu___120_13868 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13869 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13872) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13882  ->
                  match uu___121_13882 with
                  | FStar_Syntax_Syntax.Projector uu____13883 -> true
                  | uu____13886 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13889 = try_lookup_free_var env l in
          (match uu____13889 with
           | FStar_Pervasives_Native.Some uu____13893 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_13896 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13896.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13896.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_13896.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____13901) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13911) ->
          let uu____13916 = encode_sigelts env ses in
          (match uu____13916 with
           | (g,env1) ->
               let uu____13926 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13940  ->
                         match uu___122_13940 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13941;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13942;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13943;_}
                             -> false
                         | uu____13945 -> true)) in
               (match uu____13926 with
                | (g',inversions) ->
                    let uu____13954 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13966  ->
                              match uu___123_13966 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13967 ->
                                  true
                              | uu____13973 -> false)) in
                    (match uu____13954 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13984,tps,k,uu____13987,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13998  ->
                    match uu___124_13998 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13999 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14006 = c in
              match uu____14006 with
              | (name,args,uu____14010,uu____14011,uu____14012) ->
                  let uu____14015 =
                    let uu____14016 =
                      let uu____14022 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14033  ->
                                match uu____14033 with
                                | (uu____14037,sort,uu____14039) -> sort)) in
                      (name, uu____14022, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14016 in
                  [uu____14015]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14057 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14062 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14062 FStar_Option.isNone)) in
            if uu____14057
            then []
            else
              (let uu____14079 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14079 with
               | (xxsym,xx) ->
                   let uu____14085 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14114  ->
                             fun l  ->
                               match uu____14114 with
                               | (out,decls) ->
                                   let uu____14126 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14126 with
                                    | (uu____14132,data_t) ->
                                        let uu____14134 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14134 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14159 =
                                                 let uu____14160 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14160.FStar_Syntax_Syntax.n in
                                               match uu____14159 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14166,indices) ->
                                                   indices
                                               | uu____14178 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14194  ->
                                                         match uu____14194
                                                         with
                                                         | (x,uu____14198) ->
                                                             let uu____14199
                                                               =
                                                               let uu____14200
                                                                 =
                                                                 let uu____14204
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14204,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14200 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14199)
                                                    env) in
                                             let uu____14206 =
                                               encode_args indices env1 in
                                             (match uu____14206 with
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
                                                      let uu____14230 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14241
                                                                 =
                                                                 let uu____14244
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14244,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14241)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14230
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14246 =
                                                      let uu____14247 =
                                                        let uu____14250 =
                                                          let uu____14251 =
                                                            let uu____14254 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14254,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14251 in
                                                        (out, uu____14250) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14247 in
                                                    (uu____14246,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14085 with
                    | (data_ax,decls) ->
                        let uu____14262 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14262 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14276 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14276 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14279 =
                                 let uu____14283 =
                                   let uu____14284 =
                                     let uu____14290 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14298 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14290,
                                       uu____14298) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14284 in
                                 let uu____14306 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14283,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____14306) in
                               FStar_SMTEncoding_Util.mkAssume uu____14279 in
                             let pattern_guarded_inversion =
                               let uu____14310 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14310
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14321 =
                                   let uu____14322 =
                                     let uu____14326 =
                                       let uu____14327 =
                                         let uu____14333 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14341 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14333, uu____14341) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14327 in
                                     let uu____14349 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14326,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____14349) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14322 in
                                 [uu____14321]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14352 =
            let uu____14359 =
              let uu____14360 = FStar_Syntax_Subst.compress k in
              uu____14360.FStar_Syntax_Syntax.n in
            match uu____14359 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14384 -> (tps, k) in
          (match uu____14352 with
           | (formals,res) ->
               let uu____14397 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14397 with
                | (formals1,res1) ->
                    let uu____14404 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____14404 with
                     | (vars,guards,env',binder_decls,uu____14419) ->
                         let uu____14426 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14426 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14439 =
                                  let uu____14443 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14443) in
                                FStar_SMTEncoding_Util.mkApp uu____14439 in
                              let uu____14448 =
                                let tname_decl =
                                  let uu____14454 =
                                    let uu____14455 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14473  ->
                                              match uu____14473 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14481 = varops.next_id () in
                                    (tname, uu____14455,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14481, false) in
                                  constructor_or_logic_type_decl uu____14454 in
                                let uu____14486 =
                                  match vars with
                                  | [] ->
                                      let uu____14493 =
                                        let uu____14494 =
                                          let uu____14496 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_43  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_43) uu____14496 in
                                        push_free_var env1 t tname
                                          uu____14494 in
                                      ([], uu____14493)
                                  | uu____14500 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____14506 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14506 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14515 =
                                          let uu____14519 =
                                            let uu____14520 =
                                              let uu____14528 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____14528) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14520 in
                                          (uu____14519,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14515 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14486 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14448 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14551 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____14551 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14568 =
                                               let uu____14569 =
                                                 let uu____14573 =
                                                   let uu____14574 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14574 in
                                                 (uu____14573,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14569 in
                                             [uu____14568]
                                           else [] in
                                         let uu____14577 =
                                           let uu____14579 =
                                             let uu____14581 =
                                               let uu____14582 =
                                                 let uu____14586 =
                                                   let uu____14587 =
                                                     let uu____14593 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14593) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14587 in
                                                 (uu____14586,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14582 in
                                             [uu____14581] in
                                           FStar_List.append karr uu____14579 in
                                         FStar_List.append decls1 uu____14577 in
                                   let aux =
                                     let uu____14602 =
                                       let uu____14604 =
                                         inversion_axioms tapp vars in
                                       let uu____14606 =
                                         let uu____14608 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14608] in
                                       FStar_List.append uu____14604
                                         uu____14606 in
                                     FStar_List.append kindingAx uu____14602 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14613,uu____14614,uu____14615,uu____14616,uu____14617)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14622,t,uu____14624,n_tps,uu____14626) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14631 = new_term_constant_and_tok_from_lid env d in
          (match uu____14631 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14642 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14642 with
                | (formals,t_res) ->
                    let uu____14661 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14661 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14670 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____14670 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14712 =
                                            mk_term_projector_name d x in
                                          (uu____14712,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14714 =
                                  let uu____14724 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14724, true) in
                                FStar_All.pipe_right uu____14714
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
                              let uu____14746 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____14746 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14754::uu____14755 ->
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
                                         let uu____14780 =
                                           let uu____14786 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14786) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14780
                                     | uu____14799 -> tok_typing in
                                   let uu____14804 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____14804 with
                                    | (vars',guards',env'',decls_formals,uu____14819)
                                        ->
                                        let uu____14826 =
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
                                        (match uu____14826 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14845 ->
                                                   let uu____14849 =
                                                     let uu____14850 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14850 in
                                                   [uu____14849] in
                                             let encode_elim uu____14857 =
                                               let uu____14858 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14858 with
                                               | (head1,args) ->
                                                   let uu____14881 =
                                                     let uu____14882 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14882.FStar_Syntax_Syntax.n in
                                                   (match uu____14881 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14888;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14889;_},uu____14890)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14894 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14894
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
                                                                 | uu____14923
                                                                    ->
                                                                    let uu____14924
                                                                    =
                                                                    let uu____14925
                                                                    =
                                                                    let uu____14928
                                                                    =
                                                                    let uu____14929
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____14929 in
                                                                    (uu____14928,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____14925 in
                                                                    raise
                                                                    uu____14924 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14940
                                                                    =
                                                                    let uu____14941
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14941 in
                                                                    if
                                                                    uu____14940
                                                                    then
                                                                    let uu____14948
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14948]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14950
                                                               =
                                                               let uu____14957
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14989
                                                                     ->
                                                                    fun
                                                                    uu____14990
                                                                     ->
                                                                    match 
                                                                    (uu____14989,
                                                                    uu____14990)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15041
                                                                    =
                                                                    let uu____15045
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15045 in
                                                                    (match uu____15041
                                                                    with
                                                                    | 
                                                                    (uu____15052,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15058
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15058
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15060
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15060
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
                                                                 uu____14957 in
                                                             (match uu____14950
                                                              with
                                                              | (uu____15068,arg_vars,elim_eqns_or_guards,uu____15071)
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
                                                                    let uu____15090
                                                                    =
                                                                    let uu____15094
                                                                    =
                                                                    let uu____15095
                                                                    =
                                                                    let uu____15101
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15107
                                                                    =
                                                                    let uu____15108
                                                                    =
                                                                    let uu____15111
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15111) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15108 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15101,
                                                                    uu____15107) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15095 in
                                                                    (uu____15094,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15090 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15124
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15124,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15126
                                                                    =
                                                                    let uu____15130
                                                                    =
                                                                    let uu____15131
                                                                    =
                                                                    let uu____15137
                                                                    =
                                                                    let uu____15140
                                                                    =
                                                                    let uu____15142
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15142] in
                                                                    [uu____15140] in
                                                                    let uu____15145
                                                                    =
                                                                    let uu____15146
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15150
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15149,
                                                                    uu____15150) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15146 in
                                                                    (uu____15137,
                                                                    [x],
                                                                    uu____15145) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15131 in
                                                                    let uu____15160
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15130,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15160) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15126
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15165
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
                                                                    (let uu____15182
                                                                    =
                                                                    let uu____15183
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15183
                                                                    dapp1 in
                                                                    [uu____15182]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15165
                                                                    FStar_List.flatten in
                                                                    let uu____15187
                                                                    =
                                                                    let uu____15191
                                                                    =
                                                                    let uu____15192
                                                                    =
                                                                    let uu____15198
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15204
                                                                    =
                                                                    let uu____15205
                                                                    =
                                                                    let uu____15208
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15208) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15205 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15198,
                                                                    uu____15204) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15192 in
                                                                    (uu____15191,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15187) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15220 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15220
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
                                                                 | uu____15249
                                                                    ->
                                                                    let uu____15250
                                                                    =
                                                                    let uu____15251
                                                                    =
                                                                    let uu____15254
                                                                    =
                                                                    let uu____15255
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15255 in
                                                                    (uu____15254,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15251 in
                                                                    raise
                                                                    uu____15250 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15266
                                                                    =
                                                                    let uu____15267
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15267 in
                                                                    if
                                                                    uu____15266
                                                                    then
                                                                    let uu____15274
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15274]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15276
                                                               =
                                                               let uu____15283
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15315
                                                                     ->
                                                                    fun
                                                                    uu____15316
                                                                     ->
                                                                    match 
                                                                    (uu____15315,
                                                                    uu____15316)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15367
                                                                    =
                                                                    let uu____15371
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15371 in
                                                                    (match uu____15367
                                                                    with
                                                                    | 
                                                                    (uu____15378,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15384
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15384
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15386
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15386
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
                                                                 uu____15283 in
                                                             (match uu____15276
                                                              with
                                                              | (uu____15394,arg_vars,elim_eqns_or_guards,uu____15397)
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
                                                                    let uu____15416
                                                                    =
                                                                    let uu____15420
                                                                    =
                                                                    let uu____15421
                                                                    =
                                                                    let uu____15427
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15433
                                                                    =
                                                                    let uu____15434
                                                                    =
                                                                    let uu____15437
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15437) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15434 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15427,
                                                                    uu____15433) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15421 in
                                                                    (uu____15420,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15416 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15450
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15450,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15452
                                                                    =
                                                                    let uu____15456
                                                                    =
                                                                    let uu____15457
                                                                    =
                                                                    let uu____15463
                                                                    =
                                                                    let uu____15466
                                                                    =
                                                                    let uu____15468
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15468] in
                                                                    [uu____15466] in
                                                                    let uu____15471
                                                                    =
                                                                    let uu____15472
                                                                    =
                                                                    let uu____15475
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15476
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15475,
                                                                    uu____15476) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15472 in
                                                                    (uu____15463,
                                                                    [x],
                                                                    uu____15471) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15457 in
                                                                    let uu____15486
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15456,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15486) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15452
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15491
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
                                                                    (let uu____15508
                                                                    =
                                                                    let uu____15509
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15509
                                                                    dapp1 in
                                                                    [uu____15508]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15491
                                                                    FStar_List.flatten in
                                                                    let uu____15513
                                                                    =
                                                                    let uu____15517
                                                                    =
                                                                    let uu____15518
                                                                    =
                                                                    let uu____15524
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15530
                                                                    =
                                                                    let uu____15531
                                                                    =
                                                                    let uu____15534
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15534) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15531 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15524,
                                                                    uu____15530) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15518 in
                                                                    (uu____15517,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15513) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15544 ->
                                                        ((let uu____15546 =
                                                            let uu____15547 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15548 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15547
                                                              uu____15548 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15546);
                                                         ([], []))) in
                                             let uu____15551 = encode_elim () in
                                             (match uu____15551 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15563 =
                                                      let uu____15565 =
                                                        let uu____15567 =
                                                          let uu____15569 =
                                                            let uu____15571 =
                                                              let uu____15572
                                                                =
                                                                let uu____15578
                                                                  =
                                                                  let uu____15580
                                                                    =
                                                                    let uu____15581
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15581 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15580 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15578) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15572 in
                                                            [uu____15571] in
                                                          let uu____15584 =
                                                            let uu____15586 =
                                                              let uu____15588
                                                                =
                                                                let uu____15590
                                                                  =
                                                                  let uu____15592
                                                                    =
                                                                    let uu____15594
                                                                    =
                                                                    let uu____15596
                                                                    =
                                                                    let uu____15597
                                                                    =
                                                                    let uu____15601
                                                                    =
                                                                    let uu____15602
                                                                    =
                                                                    let uu____15608
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15608) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15602 in
                                                                    (uu____15601,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15597 in
                                                                    let uu____15615
                                                                    =
                                                                    let uu____15617
                                                                    =
                                                                    let uu____15618
                                                                    =
                                                                    let uu____15622
                                                                    =
                                                                    let uu____15623
                                                                    =
                                                                    let uu____15629
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15635
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15629,
                                                                    uu____15635) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15623 in
                                                                    (uu____15622,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15618 in
                                                                    [uu____15617] in
                                                                    uu____15596
                                                                    ::
                                                                    uu____15615 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15594 in
                                                                  FStar_List.append
                                                                    uu____15592
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15590 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15588 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15586 in
                                                          FStar_List.append
                                                            uu____15569
                                                            uu____15584 in
                                                        FStar_List.append
                                                          decls3 uu____15567 in
                                                      FStar_List.append
                                                        decls2 uu____15565 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15563 in
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
           (fun uu____15663  ->
              fun se  ->
                match uu____15663 with
                | (g,env1) ->
                    let uu____15675 = encode_sigelt env1 se in
                    (match uu____15675 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15713 =
        match uu____15713 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15731 ->
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
                 ((let uu____15736 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15736
                   then
                     let uu____15737 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15738 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15739 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15737 uu____15738 uu____15739
                   else ());
                  (let uu____15741 = encode_term t1 env1 in
                   match uu____15741 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15751 =
                         let uu____15755 =
                           let uu____15756 =
                             let uu____15757 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15757
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15756 in
                         new_term_constant_from_string env1 x uu____15755 in
                       (match uu____15751 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____15768 = FStar_Options.log_queries () in
                              if uu____15768
                              then
                                let uu____15770 =
                                  let uu____15771 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15772 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15773 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15771 uu____15772 uu____15773 in
                                FStar_Pervasives_Native.Some uu____15770
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15784,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____15793 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15793 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15806,se,uu____15808) ->
                 let uu____15811 = encode_sigelt env1 se in
                 (match uu____15811 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15821,se) ->
                 let uu____15825 = encode_sigelt env1 se in
                 (match uu____15825 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15835 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15835 with | (uu____15847,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15899  ->
            match uu____15899 with
            | (l,uu____15906,uu____15907) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15934  ->
            match uu____15934 with
            | (l,uu____15942,uu____15943) ->
                let uu____15948 =
                  FStar_All.pipe_left
                    (fun _0_44  -> FStar_SMTEncoding_Term.Echo _0_44)
                    (FStar_Pervasives_Native.fst l) in
                let uu____15949 =
                  let uu____15951 =
                    let uu____15952 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15952 in
                  [uu____15951] in
                uu____15948 :: uu____15949)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15964 =
      let uu____15966 =
        let uu____15967 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15969 =
          let uu____15970 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15970 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15967;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15969
        } in
      [uu____15966] in
    FStar_ST.write last_env uu____15964
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15982 = FStar_ST.read last_env in
      match uu____15982 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15988 ->
          let uu___153_15990 = e in
          let uu____15991 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15990.bindings);
            depth = (uu___153_15990.depth);
            tcenv;
            warn = (uu___153_15990.warn);
            cache = (uu___153_15990.cache);
            nolabels = (uu___153_15990.nolabels);
            use_zfuel_name = (uu___153_15990.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15990.encode_non_total_function_typ);
            current_module_name = uu____15991
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15996 = FStar_ST.read last_env in
    match uu____15996 with
    | [] -> failwith "Empty env stack"
    | uu____16001::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16010  ->
    let uu____16011 = FStar_ST.read last_env in
    match uu____16011 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_16022 = hd1 in
          {
            bindings = (uu___154_16022.bindings);
            depth = (uu___154_16022.depth);
            tcenv = (uu___154_16022.tcenv);
            warn = (uu___154_16022.warn);
            cache = refs;
            nolabels = (uu___154_16022.nolabels);
            use_zfuel_name = (uu___154_16022.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16022.encode_non_total_function_typ);
            current_module_name = (uu___154_16022.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16029  ->
    let uu____16030 = FStar_ST.read last_env in
    match uu____16030 with
    | [] -> failwith "Popping an empty stack"
    | uu____16035::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16044  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16048  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16052  ->
    let uu____16053 = FStar_ST.read last_env in
    match uu____16053 with
    | hd1::uu____16059::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16065 -> failwith "Impossible"
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
        | (uu____16124::uu____16125,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16131 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16131.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16131.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16131.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16132 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16145 =
        let uu____16147 =
          let uu____16148 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16148 in
        let uu____16149 = open_fact_db_tags env in uu____16147 :: uu____16149 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16145
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
      let uu____16166 = encode_sigelt env se in
      match uu____16166 with
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
        let uu____16193 = FStar_Options.log_queries () in
        if uu____16193
        then
          let uu____16195 =
            let uu____16196 =
              let uu____16197 =
                let uu____16198 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16198 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16197 in
            FStar_SMTEncoding_Term.Caption uu____16196 in
          uu____16195 :: decls
        else decls in
      let env =
        let uu____16205 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16205 tcenv in
      let uu____16206 = encode_top_level_facts env se in
      match uu____16206 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16215 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16215))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16228 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16228
       then
         let uu____16229 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16229
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16259  ->
                 fun se  ->
                   match uu____16259 with
                   | (g,env2) ->
                       let uu____16271 = encode_top_level_facts env2 se in
                       (match uu____16271 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16284 =
         encode_signature
           (let uu___156_16290 = env in
            {
              bindings = (uu___156_16290.bindings);
              depth = (uu___156_16290.depth);
              tcenv = (uu___156_16290.tcenv);
              warn = false;
              cache = (uu___156_16290.cache);
              nolabels = (uu___156_16290.nolabels);
              use_zfuel_name = (uu___156_16290.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16290.encode_non_total_function_typ);
              current_module_name = (uu___156_16290.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16284 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16302 = FStar_Options.log_queries () in
             if uu____16302
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16309 = env1 in
               {
                 bindings = (uu___157_16309.bindings);
                 depth = (uu___157_16309.depth);
                 tcenv = (uu___157_16309.tcenv);
                 warn = true;
                 cache = (uu___157_16309.cache);
                 nolabels = (uu___157_16309.nolabels);
                 use_zfuel_name = (uu___157_16309.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16309.encode_non_total_function_typ);
                 current_module_name = (uu___157_16309.current_module_name)
               });
            (let uu____16311 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16311
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
        (let uu____16349 =
           let uu____16350 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16350.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16349);
        (let env =
           let uu____16352 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16352 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16361 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16382 = aux rest in
                 (match uu____16382 with
                  | (out,rest1) ->
                      let t =
                        let uu____16399 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16399 with
                        | FStar_Pervasives_Native.Some uu____16402 ->
                            let uu____16403 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16403
                              x.FStar_Syntax_Syntax.sort
                        | uu____16404 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16407 =
                        let uu____16409 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16412 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16412.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16412.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16409 :: out in
                      (uu____16407, rest1))
             | uu____16415 -> ([], bindings1) in
           let uu____16419 = aux bindings in
           match uu____16419 with
           | (closing,bindings1) ->
               let uu____16433 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16433, bindings1) in
         match uu____16361 with
         | (q1,bindings1) ->
             let uu____16446 =
               let uu____16449 =
                 FStar_List.filter
                   (fun uu___125_16453  ->
                      match uu___125_16453 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16454 ->
                          false
                      | uu____16458 -> true) bindings1 in
               encode_env_bindings env uu____16449 in
             (match uu____16446 with
              | (env_decls,env1) ->
                  ((let uu____16469 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16469
                    then
                      let uu____16470 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16470
                    else ());
                   (let uu____16472 = encode_formula q1 env1 in
                    match uu____16472 with
                    | (phi,qdecls) ->
                        let uu____16484 =
                          let uu____16487 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16487 phi in
                        (match uu____16484 with
                         | (labels,phi1) ->
                             let uu____16497 = encode_labels labels in
                             (match uu____16497 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16518 =
                                      let uu____16522 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16523 =
                                        varops.mk_unique "@query" in
                                      (uu____16522,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16523) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16518 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16538 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16538 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16540 = encode_formula q env in
       match uu____16540 with
       | (f,uu____16544) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16546) -> true
             | uu____16549 -> false)))