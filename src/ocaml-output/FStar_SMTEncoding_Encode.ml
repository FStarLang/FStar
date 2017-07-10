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
            let uu____139 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____139 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____136 in
        FStar_Util.Inl uu____135 in
      FStar_Pervasives_Native.Some uu____132
  | uu____144 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_161 = a in
        let uu____162 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____162;
          FStar_Syntax_Syntax.index =
            (uu___126_161.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_161.FStar_Syntax_Syntax.sort)
        } in
      let uu____163 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____163
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____179 =
          let uu____180 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____180 in
        let uu____181 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____181 with
        | (uu____184,t) ->
            let uu____186 =
              let uu____187 = FStar_Syntax_Subst.compress t in
              uu____187.FStar_Syntax_Syntax.n in
            (match uu____186 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____202 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____202 with
                  | (binders,uu____206) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____219 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____228 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____228
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____237 =
        let uu____240 = mk_term_projector_name lid a in
        (uu____240,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____237
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____249 =
        let uu____252 = mk_term_projector_name_by_pos lid i in
        (uu____252,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____249
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
  let new_scope uu____866 =
    let uu____867 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____869 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____867, uu____869) in
  let scopes =
    let uu____880 = let uu____886 = new_scope () in [uu____886] in
    FStar_Util.mk_ref uu____880 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____911 =
        let uu____913 = FStar_ST.read scopes in
        FStar_Util.find_map uu____913
          (fun uu____933  ->
             match uu____933 with
             | (names1,uu____940) -> FStar_Util.smap_try_find names1 y1) in
      match uu____911 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____945 ->
          (FStar_Util.incr ctr;
           (let uu____950 =
              let uu____951 =
                let uu____952 = FStar_ST.read ctr in
                Prims.string_of_int uu____952 in
              Prims.strcat "__" uu____951 in
            Prims.strcat y1 uu____950)) in
    let top_scope =
      let uu____957 =
        let uu____962 = FStar_ST.read scopes in FStar_List.hd uu____962 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____957 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____1001 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____1012 =
      let uu____1013 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1013 in
    FStar_Util.format2 "%s_%s" pfx uu____1012 in
  let string_const s =
    let uu____1018 =
      let uu____1020 = FStar_ST.read scopes in
      FStar_Util.find_map uu____1020
        (fun uu____1040  ->
           match uu____1040 with
           | (uu____1046,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1018 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____1055 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1055 in
        let top_scope =
          let uu____1058 =
            let uu____1063 = FStar_ST.read scopes in FStar_List.hd uu____1063 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1058 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1091 =
    let uu____1092 =
      let uu____1098 = new_scope () in
      let uu____1103 = FStar_ST.read scopes in uu____1098 :: uu____1103 in
    FStar_ST.write scopes uu____1092 in
  let pop1 uu____1130 =
    let uu____1131 =
      let uu____1137 = FStar_ST.read scopes in FStar_List.tl uu____1137 in
    FStar_ST.write scopes uu____1131 in
  let mark1 uu____1164 = push1 () in
  let reset_mark1 uu____1168 = pop1 () in
  let commit_mark1 uu____1172 =
    let uu____1173 = FStar_ST.read scopes in
    match uu____1173 with
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
    | uu____1239 -> failwith "Impossible" in
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
    let uu___127_1249 = x in
    let uu____1250 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1250;
      FStar_Syntax_Syntax.index = (uu___127_1249.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1249.FStar_Syntax_Syntax.sort)
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
    match projectee with | Binding_var _0 -> true | uu____1274 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1300 -> false
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
         (fun uu___103_1626  ->
            match uu___103_1626 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1629 -> [])) in
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
    let uu____1639 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_1646  ->
              match uu___104_1646 with
              | Binding_var (x,uu____1648) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1650,uu____1651,uu____1652) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1639 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____1690 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1690
      then
        let uu____1692 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____1692
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
      let uu____1705 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1705)
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
        (let uu___128_1720 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1720.tcenv);
           warn = (uu___128_1720.warn);
           cache = (uu___128_1720.cache);
           nolabels = (uu___128_1720.nolabels);
           use_zfuel_name = (uu___128_1720.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1720.encode_non_total_function_typ);
           current_module_name = (uu___128_1720.current_module_name)
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
        (let uu___129_1736 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1736.depth);
           tcenv = (uu___129_1736.tcenv);
           warn = (uu___129_1736.warn);
           cache = (uu___129_1736.cache);
           nolabels = (uu___129_1736.nolabels);
           use_zfuel_name = (uu___129_1736.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1736.encode_non_total_function_typ);
           current_module_name = (uu___129_1736.current_module_name)
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
          (let uu___130_1756 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1756.depth);
             tcenv = (uu___130_1756.tcenv);
             warn = (uu___130_1756.warn);
             cache = (uu___130_1756.cache);
             nolabels = (uu___130_1756.nolabels);
             use_zfuel_name = (uu___130_1756.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1756.encode_non_total_function_typ);
             current_module_name = (uu___130_1756.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1769 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1769.depth);
          tcenv = (uu___131_1769.tcenv);
          warn = (uu___131_1769.warn);
          cache = (uu___131_1769.cache);
          nolabels = (uu___131_1769.nolabels);
          use_zfuel_name = (uu___131_1769.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1769.encode_non_total_function_typ);
          current_module_name = (uu___131_1769.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1790  ->
             match uu___105_1790 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____1798 -> FStar_Pervasives_Native.None) in
      let uu____1801 = aux a in
      match uu____1801 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____1808 = aux a2 in
          (match uu____1808 with
           | FStar_Pervasives_Native.None  ->
               let uu____1814 =
                 let uu____1815 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1816 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1815 uu____1816 in
               failwith uu____1814
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
      let uu____1838 =
        let uu___132_1839 = env in
        let uu____1840 =
          let uu____1842 =
            let uu____1843 =
              let uu____1850 =
                let uu____1852 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_39  -> FStar_Pervasives_Native.Some _0_39)
                  uu____1852 in
              (x, fname, uu____1850, FStar_Pervasives_Native.None) in
            Binding_fvar uu____1843 in
          uu____1842 :: (env.bindings) in
        {
          bindings = uu____1840;
          depth = (uu___132_1839.depth);
          tcenv = (uu___132_1839.tcenv);
          warn = (uu___132_1839.warn);
          cache = (uu___132_1839.cache);
          nolabels = (uu___132_1839.nolabels);
          use_zfuel_name = (uu___132_1839.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1839.encode_non_total_function_typ);
          current_module_name = (uu___132_1839.current_module_name)
        } in
      (fname, ftok, uu____1838)
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
        (fun uu___106_1881  ->
           match uu___106_1881 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____1903 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1917 =
        lookup_binding env
          (fun uu___107_1924  ->
             match uu___107_1924 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____1934 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____1917 FStar_Option.isSome
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
      let uu____1949 = try_lookup_lid env a in
      match uu____1949 with
      | FStar_Pervasives_Native.None  ->
          let uu____1966 =
            let uu____1967 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1967 in
          failwith uu____1966
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
          let uu___133_2002 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_2002.depth);
            tcenv = (uu___133_2002.tcenv);
            warn = (uu___133_2002.warn);
            cache = (uu___133_2002.cache);
            nolabels = (uu___133_2002.nolabels);
            use_zfuel_name = (uu___133_2002.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_2002.encode_non_total_function_typ);
            current_module_name = (uu___133_2002.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2017 = lookup_lid env x in
        match uu____2017 with
        | (t1,t2,uu____2025) ->
            let t3 =
              let uu____2031 =
                let uu____2035 =
                  let uu____2037 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2037] in
                (f, uu____2035) in
              FStar_SMTEncoding_Util.mkApp uu____2031 in
            let uu___134_2040 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_2040.depth);
              tcenv = (uu___134_2040.tcenv);
              warn = (uu___134_2040.warn);
              cache = (uu___134_2040.cache);
              nolabels = (uu___134_2040.nolabels);
              use_zfuel_name = (uu___134_2040.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_2040.encode_non_total_function_typ);
              current_module_name = (uu___134_2040.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2052 = try_lookup_lid env l in
      match uu____2052 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2079 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2084,fuel::[]) ->
                         let uu____2087 =
                           let uu____2088 =
                             let uu____2089 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2089
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____2088 "fuel" in
                         if uu____2087
                         then
                           let uu____2091 =
                             let uu____2092 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2092
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_40  ->
                                FStar_Pervasives_Native.Some _0_40)
                             uu____2091
                         else FStar_Pervasives_Native.Some t
                     | uu____2095 -> FStar_Pervasives_Native.Some t)
                | uu____2096 -> FStar_Pervasives_Native.None))
let lookup_free_var:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2108 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
      match uu____2108 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2111 =
            let uu____2112 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
            FStar_Util.format1 "Name not found: %s" uu____2112 in
          failwith uu____2111
let lookup_free_var_name:
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2123 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2123 with | (x,uu____2130,uu____2131) -> x
let lookup_free_var_sym:
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____2149 = lookup_lid env a.FStar_Syntax_Syntax.v in
      match uu____2149 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2170;
                 FStar_SMTEncoding_Term.rng = uu____2171;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2179 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2193 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___108_2209  ->
           match uu___108_2209 with
           | Binding_fvar (uu____2211,nm',tok,uu____2214) when nm = nm' ->
               tok
           | uu____2219 -> FStar_Pervasives_Native.None)
let mkForall_fuel' n1 uu____2239 =
  match uu____2239 with
  | (pats,vars,body) ->
      let fallback uu____2255 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2258 = FStar_Options.unthrottle_inductives () in
      if uu____2258
      then fallback ()
      else
        (let uu____2260 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2260 with
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
                       | uu____2281 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2295 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2295
                     | uu____2297 ->
                         let uu____2298 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2298 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2301 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____2330 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2338 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2343 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2344 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2355 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2365 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2367 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2367 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2377;
             FStar_Syntax_Syntax.pos = uu____2378;_},uu____2379)
          ->
          let uu____2393 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2393 FStar_Option.isNone
      | uu____2402 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2411 =
        let uu____2412 = FStar_Syntax_Util.un_uinst t in
        uu____2412.FStar_Syntax_Syntax.n in
      match uu____2411 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2415,uu____2416,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_2430  ->
                  match uu___109_2430 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2431 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2433 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2433 FStar_Option.isSome
      | uu____2442 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2451 = head_normal env t in
      if uu____2451
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
    let uu____2465 =
      let uu____2466 = FStar_Syntax_Syntax.null_binder t in [uu____2466] in
    let uu____2467 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____2465 uu____2467 FStar_Pervasives_Native.None
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
                    let uu____2494 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2494
                | s ->
                    let uu____2498 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2498) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_2513  ->
    match uu___110_2513 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2514 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2545;
                       FStar_SMTEncoding_Term.rng = uu____2546;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2560) ->
              let uu____2565 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2582 -> false) args (FStar_List.rev xs)) in
              if uu____2565
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____2585,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2588 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2592 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2592)) in
              if uu____2588
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____2595 -> FStar_Pervasives_Native.None in
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
    | uu____2762 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2766  ->
    match uu___111_2766 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2768 =
          let uu____2772 =
            let uu____2774 =
              let uu____2775 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2775 in
            [uu____2774] in
          ("FStar.Char.Char", uu____2772) in
        FStar_SMTEncoding_Util.mkApp uu____2768
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____2783 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2783
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____2785) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2794) ->
        let uu____2797 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2797
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2801 =
          let uu____2802 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2802 in
        failwith uu____2801
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2823 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2831 ->
            let uu____2836 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2836
        | uu____2837 ->
            if norm1
            then let uu____2838 = whnf env t1 in aux false uu____2838
            else
              (let uu____2840 =
                 let uu____2841 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2842 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2841 uu____2842 in
               failwith uu____2840) in
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
    | uu____2864 ->
        let uu____2865 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2865)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2897::uu____2898::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2901::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____2903 -> false
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
        (let uu____3041 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3041
         then
           let uu____3042 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3042
         else ());
        (let uu____3044 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3093  ->
                   fun b  ->
                     match uu____3093 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3136 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3145 = gen_term_var env1 x in
                           match uu____3145 with
                           | (xxsym,xx,env') ->
                               let uu____3159 =
                                 let uu____3162 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3162 env1 xx in
                               (match uu____3159 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3136 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3044 with
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
          let uu____3250 = encode_term t env in
          match uu____3250 with
          | (t1,decls) ->
              let uu____3257 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3257, decls)
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
          let uu____3265 = encode_term t env in
          match uu____3265 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3274 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3274, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3276 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3276, decls))
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
        let uu____3282 = encode_args args_e env in
        match uu____3282 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3294 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3301 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3301 in
            let binary arg_tms1 =
              let uu____3310 =
                let uu____3311 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3311 in
              let uu____3312 =
                let uu____3313 =
                  let uu____3314 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3314 in
                FStar_SMTEncoding_Term.unboxInt uu____3313 in
              (uu____3310, uu____3312) in
            let mk_default uu____3319 =
              let uu____3320 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3320 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3361 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3361
              then
                let uu____3362 = let uu____3363 = mk_args ts in op uu____3363 in
                FStar_All.pipe_right uu____3362 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3386 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3386
              then
                let uu____3387 = binary ts in
                match uu____3387 with
                | (t1,t2) ->
                    let uu____3392 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3392
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3395 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3395
                 then
                   let uu____3396 = op (binary ts) in
                   FStar_All.pipe_right uu____3396
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
            let uu____3486 =
              let uu____3492 =
                FStar_List.tryFind
                  (fun uu____3507  ->
                     match uu____3507 with
                     | (l,uu____3514) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3492 FStar_Util.must in
            (match uu____3486 with
             | (uu____3539,op) ->
                 let uu____3547 = op arg_tms in (uu____3547, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3554 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3554
       then
         let uu____3555 = FStar_Syntax_Print.tag_of_term t in
         let uu____3556 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3557 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3555 uu____3556
           uu____3557
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3561 ->
           let uu____3576 =
             let uu____3577 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3578 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3579 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3580 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3577
               uu____3578 uu____3579 uu____3580 in
           failwith uu____3576
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3583 =
             let uu____3584 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3585 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3586 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3587 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3584
               uu____3585 uu____3586 uu____3587 in
           failwith uu____3583
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3591 =
             let uu____3592 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3592 in
           failwith uu____3591
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3597) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3627) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3636 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3636, [])
       | FStar_Syntax_Syntax.Tm_type uu____3638 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3641) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3647 = encode_const c in (uu____3647, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3662 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3662 with
            | (binders1,res) ->
                let uu____3669 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3669
                then
                  let uu____3672 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____3672 with
                   | (vars,guards,env',decls,uu____3687) ->
                       let fsym =
                         let uu____3697 = varops.fresh "f" in
                         (uu____3697, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3700 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3706 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3706.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3706.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3706.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3706.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3706.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3706.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3706.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3706.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3706.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3706.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3706.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3706.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3706.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3706.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3706.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3706.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3706.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3706.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3706.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3706.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3706.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3706.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3706.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3706.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3706.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3706.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3700 with
                        | (pre_opt,res_t) ->
                            let uu____3713 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____3713 with
                             | (res_pred,decls') ->
                                 let uu____3720 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3727 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3727, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3730 =
                                         encode_formula pre env' in
                                       (match uu____3730 with
                                        | (guard,decls0) ->
                                            let uu____3738 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3738, decls0)) in
                                 (match uu____3720 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3746 =
                                          let uu____3752 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3752) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3746 in
                                      let cvars =
                                        let uu____3762 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3762
                                          (FStar_List.filter
                                             (fun uu____3771  ->
                                                match uu____3771 with
                                                | (x,uu____3775) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3786 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3786 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3791 =
                                             let uu____3792 =
                                               let uu____3796 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3796) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3792 in
                                           (uu____3791,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3807 =
                                               let uu____3808 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3808 in
                                             varops.mk_unique uu____3807 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____3815 =
                                               FStar_Options.log_queries () in
                                             if uu____3815
                                             then
                                               let uu____3817 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3817
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3823 =
                                               let uu____3827 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3827) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3823 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3835 =
                                               let uu____3839 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3839,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3835 in
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
                                             let uu____3852 =
                                               let uu____3856 =
                                                 let uu____3857 =
                                                   let uu____3863 =
                                                     let uu____3864 =
                                                       let uu____3867 =
                                                         let uu____3868 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3868 in
                                                       (f_has_t, uu____3867) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3864 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3863) in
                                                 mkForall_fuel uu____3857 in
                                               (uu____3856,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3852 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3881 =
                                               let uu____3885 =
                                                 let uu____3886 =
                                                   let uu____3892 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3892) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3886 in
                                               (uu____3885,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3881 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3906 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3906);
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
                     let uu____3917 =
                       let uu____3921 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3921,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3917 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3930 =
                       let uu____3934 =
                         let uu____3935 =
                           let uu____3941 =
                             let uu____3942 =
                               let uu____3945 =
                                 let uu____3946 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3946 in
                               (f_has_t, uu____3945) in
                             FStar_SMTEncoding_Util.mkImp uu____3942 in
                           ([[f_has_t]], [fsym], uu____3941) in
                         mkForall_fuel uu____3935 in
                       (uu____3934, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3930 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3960 ->
           let uu____3965 =
             let uu____3968 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3968 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3973;
                 FStar_Syntax_Syntax.pos = uu____3974;_} ->
                 let uu____3980 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____3980 with
                  | (b,f1) ->
                      let uu____3994 =
                        let uu____3995 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____3995 in
                      (uu____3994, f1))
             | uu____4000 -> failwith "impossible" in
           (match uu____3965 with
            | (x,f) ->
                let uu____4007 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4007 with
                 | (base_t,decls) ->
                     let uu____4014 = gen_term_var env x in
                     (match uu____4014 with
                      | (x1,xtm,env') ->
                          let uu____4023 = encode_formula f env' in
                          (match uu____4023 with
                           | (refinement,decls') ->
                               let uu____4030 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4030 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4041 =
                                        let uu____4043 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4047 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4043
                                          uu____4047 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4041 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4066  ->
                                              match uu____4066 with
                                              | (y,uu____4070) ->
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
                                    let uu____4089 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4089 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4094 =
                                           let uu____4095 =
                                             let uu____4099 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4099) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4095 in
                                         (uu____4094,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4111 =
                                             let uu____4112 =
                                               let uu____4113 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4113 in
                                             Prims.strcat module_name
                                               uu____4112 in
                                           varops.mk_unique uu____4111 in
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
                                           let uu____4122 =
                                             let uu____4126 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4126) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4122 in
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
                                           let uu____4137 =
                                             let uu____4141 =
                                               let uu____4142 =
                                                 let uu____4148 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4148) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4142 in
                                             (uu____4141,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4137 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4163 =
                                             let uu____4167 =
                                               let uu____4168 =
                                                 let uu____4174 =
                                                   let uu____4175 =
                                                     let uu____4178 =
                                                       let uu____4179 =
                                                         let uu____4185 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4185) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4179 in
                                                     (uu____4178, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4175 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4174) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4168 in
                                             (uu____4167,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4163 in
                                         let t_kinding =
                                           let uu____4205 =
                                             let uu____4209 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4209,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4205 in
                                         let t_interp =
                                           let uu____4219 =
                                             let uu____4223 =
                                               let uu____4224 =
                                                 let uu____4230 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4230) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4224 in
                                             let uu____4242 =
                                               let uu____4244 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4244 in
                                             (uu____4223, uu____4242,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4219 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4249 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4249);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4270 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4270 in
           let uu____4271 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4271 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4279 =
                    let uu____4283 =
                      let uu____4284 =
                        let uu____4285 =
                          let uu____4286 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4286 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4285 in
                      varops.mk_unique uu____4284 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4283) in
                  FStar_SMTEncoding_Util.mkAssume uu____4279 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4289 ->
           let uu____4299 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4299 with
            | (head1,args_e) ->
                let uu____4327 =
                  let uu____4335 =
                    let uu____4336 = FStar_Syntax_Subst.compress head1 in
                    uu____4336.FStar_Syntax_Syntax.n in
                  (uu____4335, args_e) in
                (match uu____4327 with
                 | uu____4346 when head_redex env head1 ->
                     let uu____4354 = whnf env t in
                     encode_term uu____4354 env
                 | uu____4355 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4368;
                       FStar_Syntax_Syntax.pos = uu____4369;_},uu____4370),uu____4371::
                    (v1,uu____4373)::(v2,uu____4375)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4412 = encode_term v1 env in
                     (match uu____4412 with
                      | (v11,decls1) ->
                          let uu____4419 = encode_term v2 env in
                          (match uu____4419 with
                           | (v21,decls2) ->
                               let uu____4426 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4426,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4429::(v1,uu____4431)::(v2,uu____4433)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4467 = encode_term v1 env in
                     (match uu____4467 with
                      | (v11,decls1) ->
                          let uu____4474 = encode_term v2 env in
                          (match uu____4474 with
                           | (v21,decls2) ->
                               let uu____4481 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4481,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4483) ->
                     let e0 =
                       let uu____4495 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4495 in
                     ((let uu____4501 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4501
                       then
                         let uu____4502 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4502
                       else ());
                      (let e =
                         let uu____4507 =
                           let uu____4508 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4509 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4508
                             uu____4509 in
                         uu____4507 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4518),(arg,uu____4520)::[]) -> encode_term arg env
                 | uu____4538 ->
                     let uu____4546 = encode_args args_e env in
                     (match uu____4546 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4579 = encode_term head1 env in
                            match uu____4579 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____4618 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4618 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4668  ->
                                                 fun uu____4669  ->
                                                   match (uu____4668,
                                                           uu____4669)
                                                   with
                                                   | ((bv,uu____4683),
                                                      (a,uu____4685)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4699 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4699
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4704 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____4704 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4714 =
                                                   let uu____4718 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4723 =
                                                     let uu____4724 =
                                                       let uu____4725 =
                                                         let uu____4726 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4726 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4725 in
                                                     varops.mk_unique
                                                       uu____4724 in
                                                   (uu____4718,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____4723) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4714 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4737 = lookup_free_var_sym env fv in
                            match uu____4737 with
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
                                   FStar_Syntax_Syntax.tk = uu____4758;
                                   FStar_Syntax_Syntax.pos = uu____4759;_},uu____4760)
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
                                   FStar_Syntax_Syntax.tk = uu____4770;
                                   FStar_Syntax_Syntax.pos = uu____4771;_},uu____4772)
                                ->
                                let uu____4776 =
                                  let uu____4777 =
                                    let uu____4780 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4780
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4777
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4776
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4796 =
                                  let uu____4797 =
                                    let uu____4800 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4800
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4797
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4796
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4815,(FStar_Util.Inl t1,uu____4817),uu____4818)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4856,(FStar_Util.Inr c,uu____4858),uu____4859)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____4897 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____4917 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4917 in
                               let uu____4918 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4918 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4928;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4929;_},uu____4930)
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
                                     | uu____4955 ->
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
           let uu____4995 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4995 with
            | (bs1,body1,opening) ->
                let fallback uu____5010 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____5015 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5015, [decl]) in
                let is_impure rc =
                  let uu____5021 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5021 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5030 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5030
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____5043 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____5043
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____5046 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____5046)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5051 =
                         let uu____5052 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5052 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5051);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5054 =
                       (is_impure rc) &&
                         (let uu____5056 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5056) in
                     if uu____5054
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5061 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____5061 with
                        | (vars,guards,envbody,decls,uu____5076) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5084 = encode_term body2 envbody in
                            (match uu____5084 with
                             | (body3,decls') ->
                                 let uu____5091 =
                                   let uu____5096 = codomain_eff rc in
                                   match uu____5096 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5108 = encode_term tfun env in
                                       (match uu____5108 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____5091 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5127 =
                                          let uu____5133 =
                                            let uu____5134 =
                                              let uu____5137 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5137, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5134 in
                                          ([], vars, uu____5133) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5127 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____5145 =
                                              let uu____5147 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5147
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5145 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5158 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5158 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5163 =
                                             let uu____5164 =
                                               let uu____5168 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5168) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5164 in
                                           (uu____5163,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5174 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5174 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5181 =
                                                    let uu____5182 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5182 = cache_size in
                                                  if uu____5181
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
                                                    let uu____5193 =
                                                      let uu____5194 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5194 in
                                                    varops.mk_unique
                                                      uu____5193 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5199 =
                                                    let uu____5203 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5203) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5199 in
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
                                                      let uu____5215 =
                                                        let uu____5216 =
                                                          let uu____5220 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5220,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5216 in
                                                      [uu____5215] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5228 =
                                                    let uu____5232 =
                                                      let uu____5233 =
                                                        let uu____5239 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5239) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5233 in
                                                    (uu____5232,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5228 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5249 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5249);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5251,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5252;
                          FStar_Syntax_Syntax.lbunivs = uu____5253;
                          FStar_Syntax_Syntax.lbtyp = uu____5254;
                          FStar_Syntax_Syntax.lbeff = uu____5255;
                          FStar_Syntax_Syntax.lbdef = uu____5256;_}::uu____5257),uu____5258)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5276;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5278;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5294 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5307 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5307, [decl_e])))
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
              let uu____5347 = encode_term e1 env in
              match uu____5347 with
              | (ee1,decls1) ->
                  let uu____5354 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____5354 with
                   | (xs,e21) ->
                       let uu____5368 = FStar_List.hd xs in
                       (match uu____5368 with
                        | (x1,uu____5376) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5378 = encode_body e21 env' in
                            (match uu____5378 with
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
            let uu____5400 =
              let uu____5404 =
                let uu____5405 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5405 in
              gen_term_var env uu____5404 in
            match uu____5400 with
            | (scrsym,scr',env1) ->
                let uu____5415 = encode_term e env1 in
                (match uu____5415 with
                 | (scr,decls) ->
                     let uu____5422 =
                       let encode_branch b uu____5438 =
                         match uu____5438 with
                         | (else_case,decls1) ->
                             let uu____5449 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5449 with
                              | (p,w,br) ->
                                  let uu____5468 = encode_pat env1 p in
                                  (match uu____5468 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5492  ->
                                                   match uu____5492 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5497 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____5512 =
                                               encode_term w1 env2 in
                                             (match uu____5512 with
                                              | (w2,decls2) ->
                                                  let uu____5520 =
                                                    let uu____5521 =
                                                      let uu____5524 =
                                                        let uu____5525 =
                                                          let uu____5528 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5528) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5525 in
                                                      (guard, uu____5524) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5521 in
                                                  (uu____5520, decls2)) in
                                       (match uu____5497 with
                                        | (guard1,decls2) ->
                                            let uu____5536 =
                                              encode_br br env2 in
                                            (match uu____5536 with
                                             | (br1,decls3) ->
                                                 let uu____5544 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5544,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5422 with
                      | (match_tm,decls1) ->
                          let uu____5555 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5555, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____5577 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5577
       then
         let uu____5578 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5578
       else ());
      (let uu____5580 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5580 with
       | (vars,pat_term) ->
           let uu____5590 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5621  ->
                     fun v1  ->
                       match uu____5621 with
                       | (env1,vars1) ->
                           let uu____5649 = gen_term_var env1 v1 in
                           (match uu____5649 with
                            | (xx,uu____5661,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5590 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5706 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5707 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5708 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5714 =
                        let uu____5717 = encode_const c in
                        (scrutinee, uu____5717) in
                      FStar_SMTEncoding_Util.mkEq uu____5714
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5730 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5730 with
                        | (uu____5734,uu____5735::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5737 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5758  ->
                                  match uu____5758 with
                                  | (arg,uu____5763) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5767 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5767)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5785) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5804 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5817 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5843  ->
                                  match uu____5843 with
                                  | (arg,uu____5851) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5855 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5855)) in
                      FStar_All.pipe_right uu____5817 FStar_List.flatten in
                let pat_term1 uu____5871 = encode_term pat_term env1 in
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
      let uu____5878 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5902  ->
                fun uu____5903  ->
                  match (uu____5902, uu____5903) with
                  | ((tms,decls),(t,uu____5923)) ->
                      let uu____5934 = encode_term t env in
                      (match uu____5934 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5878 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5968 = FStar_Syntax_Util.list_elements e in
        match uu____5968 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5983 =
          let uu____5993 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5993 FStar_Syntax_Util.head_and_args in
        match uu____5983 with
        | (head1,args) ->
            let uu____6021 =
              let uu____6029 =
                let uu____6030 = FStar_Syntax_Util.un_uinst head1 in
                uu____6030.FStar_Syntax_Syntax.n in
              (uu____6029, args) in
            (match uu____6021 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6041,uu____6042)::(e,uu____6044)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____6070 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6097 =
            let uu____6107 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6107 FStar_Syntax_Util.head_and_args in
          match uu____6097 with
          | (head1,args) ->
              let uu____6136 =
                let uu____6144 =
                  let uu____6145 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6145.FStar_Syntax_Syntax.n in
                (uu____6144, args) in
              (match uu____6136 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6158)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____6178 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____6193 = smt_pat_or1 t1 in
            (match uu____6193 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____6206 = list_elements1 e in
                 FStar_All.pipe_right uu____6206
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6219 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6219
                           (FStar_List.map one_pat)))
             | uu____6227 ->
                 let uu____6231 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6231])
        | uu____6247 ->
            let uu____6249 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6249] in
      let uu____6265 =
        let uu____6278 =
          let uu____6279 = FStar_Syntax_Subst.compress t in
          uu____6279.FStar_Syntax_Syntax.n in
        match uu____6278 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6306 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6306 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6335;
                        FStar_Syntax_Syntax.effect_name = uu____6336;
                        FStar_Syntax_Syntax.result_typ = uu____6337;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6339)::(post,uu____6341)::(pats,uu____6343)::[];
                        FStar_Syntax_Syntax.flags = uu____6344;_}
                      ->
                      let uu____6376 = lemma_pats pats in
                      (binders1, pre, post, uu____6376)
                  | uu____6389 -> failwith "impos"))
        | uu____6402 -> failwith "Impos" in
      match uu____6265 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6438 = env in
            {
              bindings = (uu___136_6438.bindings);
              depth = (uu___136_6438.depth);
              tcenv = (uu___136_6438.tcenv);
              warn = (uu___136_6438.warn);
              cache = (uu___136_6438.cache);
              nolabels = (uu___136_6438.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6438.encode_non_total_function_typ);
              current_module_name = (uu___136_6438.current_module_name)
            } in
          let uu____6439 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____6439 with
           | (vars,guards,env2,decls,uu____6454) ->
               let uu____6461 =
                 let uu____6468 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6494 =
                             let uu____6499 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6499 FStar_List.unzip in
                           match uu____6494 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6468 FStar_List.unzip in
               (match uu____6461 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6558 = env2 in
                      {
                        bindings = (uu___137_6558.bindings);
                        depth = (uu___137_6558.depth);
                        tcenv = (uu___137_6558.tcenv);
                        warn = (uu___137_6558.warn);
                        cache = (uu___137_6558.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6558.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6558.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6558.current_module_name)
                      } in
                    let uu____6559 =
                      let uu____6562 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6562 env3 in
                    (match uu____6559 with
                     | (pre1,decls'') ->
                         let uu____6567 =
                           let uu____6570 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6570 env3 in
                         (match uu____6567 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6577 =
                                let uu____6578 =
                                  let uu____6584 =
                                    let uu____6585 =
                                      let uu____6588 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6588, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6585 in
                                  (pats, vars, uu____6584) in
                                FStar_SMTEncoding_Util.mkForall uu____6578 in
                              (uu____6577, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6601 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6601
        then
          let uu____6602 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6603 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6602 uu____6603
        else () in
      let enc f r l =
        let uu____6630 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6648 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____6648 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6630 with
        | (decls,args) ->
            let uu____6665 =
              let uu___138_6666 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6666.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6666.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6665, decls) in
      let const_op f r uu____6691 = let uu____6700 = f r in (uu____6700, []) in
      let un_op f l =
        let uu____6716 = FStar_List.hd l in FStar_All.pipe_left f uu____6716 in
      let bin_op f uu___112_6729 =
        match uu___112_6729 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6737 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6764 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6780  ->
                 match uu____6780 with
                 | (t,uu____6788) ->
                     let uu____6789 = encode_formula t env in
                     (match uu____6789 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6764 with
        | (decls,phis) ->
            let uu____6806 =
              let uu___139_6807 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6807.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6807.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6806, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6850  ->
               match uu____6850 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____6864) -> false
                    | uu____6865 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6878 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6878
        else
          (let uu____6893 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6893 r rf) in
      let mk_imp1 r uu___113_6912 =
        match uu___113_6912 with
        | (lhs,uu____6916)::(rhs,uu____6918)::[] ->
            let uu____6939 = encode_formula rhs env in
            (match uu____6939 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6948) ->
                      (l1, decls1)
                  | uu____6951 ->
                      let uu____6952 = encode_formula lhs env in
                      (match uu____6952 with
                       | (l2,decls2) ->
                           let uu____6959 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6959, (FStar_List.append decls1 decls2)))))
        | uu____6961 -> failwith "impossible" in
      let mk_ite r uu___114_6976 =
        match uu___114_6976 with
        | (guard,uu____6980)::(_then,uu____6982)::(_else,uu____6984)::[] ->
            let uu____7013 = encode_formula guard env in
            (match uu____7013 with
             | (g,decls1) ->
                 let uu____7020 = encode_formula _then env in
                 (match uu____7020 with
                  | (t,decls2) ->
                      let uu____7027 = encode_formula _else env in
                      (match uu____7027 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7036 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7055 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7055 in
      let connectives =
        let uu____7067 =
          let uu____7076 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____7076) in
        let uu____7089 =
          let uu____7099 =
            let uu____7108 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____7108) in
          let uu____7121 =
            let uu____7131 =
              let uu____7141 =
                let uu____7150 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____7150) in
              let uu____7163 =
                let uu____7173 =
                  let uu____7183 =
                    let uu____7192 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____7192) in
                  [uu____7183;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____7173 in
              uu____7141 :: uu____7163 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____7131 in
          uu____7099 :: uu____7121 in
        uu____7067 :: uu____7089 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7408 = encode_formula phi' env in
            (match uu____7408 with
             | (phi2,decls) ->
                 let uu____7415 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7415, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7416 ->
            let uu____7421 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7421 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7448 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7448 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7456;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7458;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7474 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7474 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7506::(x,uu____7508)::(t,uu____7510)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____7544 = encode_term x env in
                 (match uu____7544 with
                  | (x1,decls) ->
                      let uu____7551 = encode_term t env in
                      (match uu____7551 with
                       | (t1,decls') ->
                           let uu____7558 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7558, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7562)::(msg,uu____7564)::(phi2,uu____7566)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____7600 =
                   let uu____7603 =
                     let uu____7604 = FStar_Syntax_Subst.compress r in
                     uu____7604.FStar_Syntax_Syntax.n in
                   let uu____7607 =
                     let uu____7608 = FStar_Syntax_Subst.compress msg in
                     uu____7608.FStar_Syntax_Syntax.n in
                   (uu____7603, uu____7607) in
                 (match uu____7600 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7615))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____7627 -> fallback phi2)
             | uu____7630 when head_redex env head2 ->
                 let uu____7638 = whnf env phi1 in
                 encode_formula uu____7638 env
             | uu____7639 ->
                 let uu____7647 = encode_term phi1 env in
                 (match uu____7647 with
                  | (tt,decls) ->
                      let uu____7654 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7657 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7657.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7657.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7654, decls)))
        | uu____7660 ->
            let uu____7661 = encode_term phi1 env in
            (match uu____7661 with
             | (tt,decls) ->
                 let uu____7668 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7671 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7671.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7671.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7668, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7698 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____7698 with
        | (vars,guards,env2,decls,uu____7720) ->
            let uu____7727 =
              let uu____7734 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7761 =
                          let uu____7766 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7783  ->
                                    match uu____7783 with
                                    | (t,uu____7789) ->
                                        encode_term t
                                          (let uu___142_7791 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7791.bindings);
                                             depth = (uu___142_7791.depth);
                                             tcenv = (uu___142_7791.tcenv);
                                             warn = (uu___142_7791.warn);
                                             cache = (uu___142_7791.cache);
                                             nolabels =
                                               (uu___142_7791.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7791.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7791.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7766 FStar_List.unzip in
                        match uu____7761 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7734 FStar_List.unzip in
            (match uu____7727 with
             | (pats,decls') ->
                 let uu____7843 = encode_formula body env2 in
                 (match uu____7843 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7862;
                             FStar_SMTEncoding_Term.rng = uu____7863;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____7871 -> guards in
                      let uu____7874 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7874, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7911  ->
                   match uu____7911 with
                   | (x,uu____7915) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7921 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7930 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7930) uu____7921 tl1 in
             let uu____7932 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7948  ->
                       match uu____7948 with
                       | (b,uu____7952) ->
                           let uu____7953 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7953)) in
             (match uu____7932 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____7957) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7969 =
                    let uu____7970 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7970 in
                  FStar_Errors.warn pos uu____7969) in
       let uu____7971 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7971 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____7977 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8016  ->
                     match uu____8016 with
                     | (l,uu____8026) -> FStar_Ident.lid_equals op l)) in
           (match uu____7977 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____8049,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8078 = encode_q_body env vars pats body in
             match uu____8078 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8104 =
                     let uu____8110 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8110) in
                   FStar_SMTEncoding_Term.mkForall uu____8104
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8122 = encode_q_body env vars pats body in
             match uu____8122 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8147 =
                   let uu____8148 =
                     let uu____8154 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8154) in
                   FStar_SMTEncoding_Term.mkExists uu____8148
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8147, decls))))
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
  let uu____8233 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8233 with
  | (asym,a) ->
      let uu____8238 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8238 with
       | (xsym,x) ->
           let uu____8243 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8243 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8273 =
                      let uu____8279 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____8279, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8273 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____8294 =
                      let uu____8298 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8298) in
                    FStar_SMTEncoding_Util.mkApp uu____8294 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8306 =
                    let uu____8308 =
                      let uu____8310 =
                        let uu____8312 =
                          let uu____8313 =
                            let uu____8317 =
                              let uu____8318 =
                                let uu____8324 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8324) in
                              FStar_SMTEncoding_Util.mkForall uu____8318 in
                            (uu____8317, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8313 in
                        let uu____8333 =
                          let uu____8335 =
                            let uu____8336 =
                              let uu____8340 =
                                let uu____8341 =
                                  let uu____8347 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8347) in
                                FStar_SMTEncoding_Util.mkForall uu____8341 in
                              (uu____8340,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8336 in
                          [uu____8335] in
                        uu____8312 :: uu____8333 in
                      xtok_decl :: uu____8310 in
                    xname_decl :: uu____8308 in
                  (xtok1, uu____8306) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8396 =
                    let uu____8404 =
                      let uu____8410 =
                        let uu____8411 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8411 in
                      quant axy uu____8410 in
                    (FStar_Parser_Const.op_Eq, uu____8404) in
                  let uu____8417 =
                    let uu____8426 =
                      let uu____8434 =
                        let uu____8440 =
                          let uu____8441 =
                            let uu____8442 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8442 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8441 in
                        quant axy uu____8440 in
                      (FStar_Parser_Const.op_notEq, uu____8434) in
                    let uu____8448 =
                      let uu____8457 =
                        let uu____8465 =
                          let uu____8471 =
                            let uu____8472 =
                              let uu____8473 =
                                let uu____8476 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8477 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8476, uu____8477) in
                              FStar_SMTEncoding_Util.mkLT uu____8473 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8472 in
                          quant xy uu____8471 in
                        (FStar_Parser_Const.op_LT, uu____8465) in
                      let uu____8483 =
                        let uu____8492 =
                          let uu____8500 =
                            let uu____8506 =
                              let uu____8507 =
                                let uu____8508 =
                                  let uu____8511 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8512 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8511, uu____8512) in
                                FStar_SMTEncoding_Util.mkLTE uu____8508 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8507 in
                            quant xy uu____8506 in
                          (FStar_Parser_Const.op_LTE, uu____8500) in
                        let uu____8518 =
                          let uu____8527 =
                            let uu____8535 =
                              let uu____8541 =
                                let uu____8542 =
                                  let uu____8543 =
                                    let uu____8546 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8547 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8546, uu____8547) in
                                  FStar_SMTEncoding_Util.mkGT uu____8543 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8542 in
                              quant xy uu____8541 in
                            (FStar_Parser_Const.op_GT, uu____8535) in
                          let uu____8553 =
                            let uu____8562 =
                              let uu____8570 =
                                let uu____8576 =
                                  let uu____8577 =
                                    let uu____8578 =
                                      let uu____8581 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8582 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8581, uu____8582) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8578 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8577 in
                                quant xy uu____8576 in
                              (FStar_Parser_Const.op_GTE, uu____8570) in
                            let uu____8588 =
                              let uu____8597 =
                                let uu____8605 =
                                  let uu____8611 =
                                    let uu____8612 =
                                      let uu____8613 =
                                        let uu____8616 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8617 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8616, uu____8617) in
                                      FStar_SMTEncoding_Util.mkSub uu____8613 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8612 in
                                  quant xy uu____8611 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____8605) in
                              let uu____8623 =
                                let uu____8632 =
                                  let uu____8640 =
                                    let uu____8646 =
                                      let uu____8647 =
                                        let uu____8648 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8648 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8647 in
                                    quant qx uu____8646 in
                                  (FStar_Parser_Const.op_Minus, uu____8640) in
                                let uu____8654 =
                                  let uu____8663 =
                                    let uu____8671 =
                                      let uu____8677 =
                                        let uu____8678 =
                                          let uu____8679 =
                                            let uu____8682 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8683 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8682, uu____8683) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8679 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8678 in
                                      quant xy uu____8677 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____8671) in
                                  let uu____8689 =
                                    let uu____8698 =
                                      let uu____8706 =
                                        let uu____8712 =
                                          let uu____8713 =
                                            let uu____8714 =
                                              let uu____8717 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8718 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8717, uu____8718) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8714 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8713 in
                                        quant xy uu____8712 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____8706) in
                                    let uu____8724 =
                                      let uu____8733 =
                                        let uu____8741 =
                                          let uu____8747 =
                                            let uu____8748 =
                                              let uu____8749 =
                                                let uu____8752 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8753 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8752, uu____8753) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8749 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8748 in
                                          quant xy uu____8747 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____8741) in
                                      let uu____8759 =
                                        let uu____8768 =
                                          let uu____8776 =
                                            let uu____8782 =
                                              let uu____8783 =
                                                let uu____8784 =
                                                  let uu____8787 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8788 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8787, uu____8788) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8784 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8783 in
                                            quant xy uu____8782 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____8776) in
                                        let uu____8794 =
                                          let uu____8803 =
                                            let uu____8811 =
                                              let uu____8817 =
                                                let uu____8818 =
                                                  let uu____8819 =
                                                    let uu____8822 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8823 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8822, uu____8823) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8819 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8818 in
                                              quant xy uu____8817 in
                                            (FStar_Parser_Const.op_And,
                                              uu____8811) in
                                          let uu____8829 =
                                            let uu____8838 =
                                              let uu____8846 =
                                                let uu____8852 =
                                                  let uu____8853 =
                                                    let uu____8854 =
                                                      let uu____8857 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8858 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8857,
                                                        uu____8858) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8854 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8853 in
                                                quant xy uu____8852 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____8846) in
                                            let uu____8864 =
                                              let uu____8873 =
                                                let uu____8881 =
                                                  let uu____8887 =
                                                    let uu____8888 =
                                                      let uu____8889 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8889 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8888 in
                                                  quant qx uu____8887 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____8881) in
                                              [uu____8873] in
                                            uu____8838 :: uu____8864 in
                                          uu____8803 :: uu____8829 in
                                        uu____8768 :: uu____8794 in
                                      uu____8733 :: uu____8759 in
                                    uu____8698 :: uu____8724 in
                                  uu____8663 :: uu____8689 in
                                uu____8632 :: uu____8654 in
                              uu____8597 :: uu____8623 in
                            uu____8562 :: uu____8588 in
                          uu____8527 :: uu____8553 in
                        uu____8492 :: uu____8518 in
                      uu____8457 :: uu____8483 in
                    uu____8426 :: uu____8448 in
                  uu____8396 :: uu____8417 in
                let mk1 l v1 =
                  let uu____9017 =
                    let uu____9022 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9057  ->
                              match uu____9057 with
                              | (l',uu____9066) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9022
                      (FStar_Option.map
                         (fun uu____9102  ->
                            match uu____9102 with | (uu____9113,b) -> b v1)) in
                  FStar_All.pipe_right uu____9017 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9157  ->
                          match uu____9157 with
                          | (l',uu____9166) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9195 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9195 with
        | (xxsym,xx) ->
            let uu____9200 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9200 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9208 =
                   let uu____9212 =
                     let uu____9213 =
                       let uu____9219 =
                         let uu____9220 =
                           let uu____9223 =
                             let uu____9224 =
                               let uu____9227 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9227) in
                             FStar_SMTEncoding_Util.mkEq uu____9224 in
                           (xx_has_type, uu____9223) in
                         FStar_SMTEncoding_Util.mkImp uu____9220 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9219) in
                     FStar_SMTEncoding_Util.mkForall uu____9213 in
                   let uu____9240 =
                     let uu____9241 =
                       let uu____9242 =
                         let uu____9243 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9243 in
                       Prims.strcat module_name uu____9242 in
                     varops.mk_unique uu____9241 in
                   (uu____9212, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____9240) in
                 FStar_SMTEncoding_Util.mkAssume uu____9208)
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
    let uu____9277 =
      let uu____9278 =
        let uu____9282 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9282, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9278 in
    let uu____9284 =
      let uu____9286 =
        let uu____9287 =
          let uu____9291 =
            let uu____9292 =
              let uu____9298 =
                let uu____9299 =
                  let uu____9302 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9302) in
                FStar_SMTEncoding_Util.mkImp uu____9299 in
              ([[typing_pred]], [xx], uu____9298) in
            mkForall_fuel uu____9292 in
          (uu____9291, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9287 in
      [uu____9286] in
    uu____9277 :: uu____9284 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9330 =
      let uu____9331 =
        let uu____9335 =
          let uu____9336 =
            let uu____9342 =
              let uu____9345 =
                let uu____9347 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9347] in
              [uu____9345] in
            let uu____9350 =
              let uu____9351 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9351 tt in
            (uu____9342, [bb], uu____9350) in
          FStar_SMTEncoding_Util.mkForall uu____9336 in
        (uu____9335, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9331 in
    let uu____9362 =
      let uu____9364 =
        let uu____9365 =
          let uu____9369 =
            let uu____9370 =
              let uu____9376 =
                let uu____9377 =
                  let uu____9380 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9380) in
                FStar_SMTEncoding_Util.mkImp uu____9377 in
              ([[typing_pred]], [xx], uu____9376) in
            mkForall_fuel uu____9370 in
          (uu____9369, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9365 in
      [uu____9364] in
    uu____9330 :: uu____9362 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9414 =
        let uu____9415 =
          let uu____9419 =
            let uu____9421 =
              let uu____9423 =
                let uu____9425 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9426 =
                  let uu____9428 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9428] in
                uu____9425 :: uu____9426 in
              tt :: uu____9423 in
            tt :: uu____9421 in
          ("Prims.Precedes", uu____9419) in
        FStar_SMTEncoding_Util.mkApp uu____9415 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9414 in
    let precedes_y_x =
      let uu____9431 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9431 in
    let uu____9433 =
      let uu____9434 =
        let uu____9438 =
          let uu____9439 =
            let uu____9445 =
              let uu____9448 =
                let uu____9450 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9450] in
              [uu____9448] in
            let uu____9453 =
              let uu____9454 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9454 tt in
            (uu____9445, [bb], uu____9453) in
          FStar_SMTEncoding_Util.mkForall uu____9439 in
        (uu____9438, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9434 in
    let uu____9465 =
      let uu____9467 =
        let uu____9468 =
          let uu____9472 =
            let uu____9473 =
              let uu____9479 =
                let uu____9480 =
                  let uu____9483 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9483) in
                FStar_SMTEncoding_Util.mkImp uu____9480 in
              ([[typing_pred]], [xx], uu____9479) in
            mkForall_fuel uu____9473 in
          (uu____9472, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9468 in
      let uu____9496 =
        let uu____9498 =
          let uu____9499 =
            let uu____9503 =
              let uu____9504 =
                let uu____9510 =
                  let uu____9511 =
                    let uu____9514 =
                      let uu____9515 =
                        let uu____9517 =
                          let uu____9519 =
                            let uu____9521 =
                              let uu____9522 =
                                let uu____9525 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9526 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9525, uu____9526) in
                              FStar_SMTEncoding_Util.mkGT uu____9522 in
                            let uu____9527 =
                              let uu____9529 =
                                let uu____9530 =
                                  let uu____9533 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9534 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9533, uu____9534) in
                                FStar_SMTEncoding_Util.mkGTE uu____9530 in
                              let uu____9535 =
                                let uu____9537 =
                                  let uu____9538 =
                                    let uu____9541 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9542 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9541, uu____9542) in
                                  FStar_SMTEncoding_Util.mkLT uu____9538 in
                                [uu____9537] in
                              uu____9529 :: uu____9535 in
                            uu____9521 :: uu____9527 in
                          typing_pred_y :: uu____9519 in
                        typing_pred :: uu____9517 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9515 in
                    (uu____9514, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9511 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9510) in
              mkForall_fuel uu____9504 in
            (uu____9503,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9499 in
        [uu____9498] in
      uu____9467 :: uu____9496 in
    uu____9433 :: uu____9465 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9572 =
      let uu____9573 =
        let uu____9577 =
          let uu____9578 =
            let uu____9584 =
              let uu____9587 =
                let uu____9589 = FStar_SMTEncoding_Term.boxString b in
                [uu____9589] in
              [uu____9587] in
            let uu____9592 =
              let uu____9593 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9593 tt in
            (uu____9584, [bb], uu____9592) in
          FStar_SMTEncoding_Util.mkForall uu____9578 in
        (uu____9577, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9573 in
    let uu____9604 =
      let uu____9606 =
        let uu____9607 =
          let uu____9611 =
            let uu____9612 =
              let uu____9618 =
                let uu____9619 =
                  let uu____9622 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9622) in
                FStar_SMTEncoding_Util.mkImp uu____9619 in
              ([[typing_pred]], [xx], uu____9618) in
            mkForall_fuel uu____9612 in
          (uu____9611, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9607 in
      [uu____9606] in
    uu____9572 :: uu____9604 in
  let mk_ref1 env reft_name uu____9644 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9655 =
        let uu____9659 =
          let uu____9661 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9661] in
        (reft_name, uu____9659) in
      FStar_SMTEncoding_Util.mkApp uu____9655 in
    let refb =
      let uu____9664 =
        let uu____9668 =
          let uu____9670 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9670] in
        (reft_name, uu____9668) in
      FStar_SMTEncoding_Util.mkApp uu____9664 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9674 =
      let uu____9675 =
        let uu____9679 =
          let uu____9680 =
            let uu____9686 =
              let uu____9687 =
                let uu____9690 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9690) in
              FStar_SMTEncoding_Util.mkImp uu____9687 in
            ([[typing_pred]], [xx; aa], uu____9686) in
          mkForall_fuel uu____9680 in
        (uu____9679, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9675 in
    [uu____9674] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9730 =
      let uu____9731 =
        let uu____9735 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9735, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9731 in
    [uu____9730] in
  let mk_and_interp env conj uu____9746 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9763 =
      let uu____9764 =
        let uu____9768 =
          let uu____9769 =
            let uu____9775 =
              let uu____9776 =
                let uu____9779 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9779, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9776 in
            ([[l_and_a_b]], [aa; bb], uu____9775) in
          FStar_SMTEncoding_Util.mkForall uu____9769 in
        (uu____9768, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9764 in
    [uu____9763] in
  let mk_or_interp env disj uu____9803 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9820 =
      let uu____9821 =
        let uu____9825 =
          let uu____9826 =
            let uu____9832 =
              let uu____9833 =
                let uu____9836 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9836, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9833 in
            ([[l_or_a_b]], [aa; bb], uu____9832) in
          FStar_SMTEncoding_Util.mkForall uu____9826 in
        (uu____9825, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9821 in
    [uu____9820] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9877 =
      let uu____9878 =
        let uu____9882 =
          let uu____9883 =
            let uu____9889 =
              let uu____9890 =
                let uu____9893 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9893, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9890 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9889) in
          FStar_SMTEncoding_Util.mkForall uu____9883 in
        (uu____9882, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9878 in
    [uu____9877] in
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
    let uu____9940 =
      let uu____9941 =
        let uu____9945 =
          let uu____9946 =
            let uu____9952 =
              let uu____9953 =
                let uu____9956 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9956, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9953 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9952) in
          FStar_SMTEncoding_Util.mkForall uu____9946 in
        (uu____9945, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9941 in
    [uu____9940] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10001 =
      let uu____10002 =
        let uu____10006 =
          let uu____10007 =
            let uu____10013 =
              let uu____10014 =
                let uu____10017 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10017, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10014 in
            ([[l_imp_a_b]], [aa; bb], uu____10013) in
          FStar_SMTEncoding_Util.mkForall uu____10007 in
        (uu____10006, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10002 in
    [uu____10001] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10058 =
      let uu____10059 =
        let uu____10063 =
          let uu____10064 =
            let uu____10070 =
              let uu____10071 =
                let uu____10074 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10074, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10071 in
            ([[l_iff_a_b]], [aa; bb], uu____10070) in
          FStar_SMTEncoding_Util.mkForall uu____10064 in
        (uu____10063, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10059 in
    [uu____10058] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10108 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10108 in
    let uu____10110 =
      let uu____10111 =
        let uu____10115 =
          let uu____10116 =
            let uu____10122 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10122) in
          FStar_SMTEncoding_Util.mkForall uu____10116 in
        (uu____10115, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10111 in
    [uu____10110] in
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
      let uu____10162 =
        let uu____10166 =
          let uu____10168 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10168] in
        ("Valid", uu____10166) in
      FStar_SMTEncoding_Util.mkApp uu____10162 in
    let uu____10170 =
      let uu____10171 =
        let uu____10175 =
          let uu____10176 =
            let uu____10182 =
              let uu____10183 =
                let uu____10186 =
                  let uu____10187 =
                    let uu____10193 =
                      let uu____10196 =
                        let uu____10198 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10198] in
                      [uu____10196] in
                    let uu____10201 =
                      let uu____10202 =
                        let uu____10205 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10205, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10202 in
                    (uu____10193, [xx1], uu____10201) in
                  FStar_SMTEncoding_Util.mkForall uu____10187 in
                (uu____10186, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10183 in
            ([[l_forall_a_b]], [aa; bb], uu____10182) in
          FStar_SMTEncoding_Util.mkForall uu____10176 in
        (uu____10175, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10171 in
    [uu____10170] in
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
      let uu____10256 =
        let uu____10260 =
          let uu____10262 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10262] in
        ("Valid", uu____10260) in
      FStar_SMTEncoding_Util.mkApp uu____10256 in
    let uu____10264 =
      let uu____10265 =
        let uu____10269 =
          let uu____10270 =
            let uu____10276 =
              let uu____10277 =
                let uu____10280 =
                  let uu____10281 =
                    let uu____10287 =
                      let uu____10290 =
                        let uu____10292 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10292] in
                      [uu____10290] in
                    let uu____10295 =
                      let uu____10296 =
                        let uu____10299 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10299, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10296 in
                    (uu____10287, [xx1], uu____10295) in
                  FStar_SMTEncoding_Util.mkExists uu____10281 in
                (uu____10280, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10277 in
            ([[l_exists_a_b]], [aa; bb], uu____10276) in
          FStar_SMTEncoding_Util.mkForall uu____10270 in
        (uu____10269, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10265 in
    [uu____10264] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10335 =
      let uu____10336 =
        let uu____10340 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10341 = varops.mk_unique "typing_range_const" in
        (uu____10340, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____10341) in
      FStar_SMTEncoding_Util.mkAssume uu____10336 in
    [uu____10335] in
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
          let uu____10603 =
            FStar_Util.find_opt
              (fun uu____10624  ->
                 match uu____10624 with
                 | (l,uu____10634) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10603 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____10656,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10692 = encode_function_type_as_formula t env in
        match uu____10692 with
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
            let uu____10725 =
              (let uu____10728 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10728) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10725
            then
              let uu____10732 = new_term_constant_and_tok_from_lid env lid in
              match uu____10732 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10744 =
                      let uu____10745 = FStar_Syntax_Subst.compress t_norm in
                      uu____10745.FStar_Syntax_Syntax.n in
                    match uu____10744 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10750) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10768  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10771 -> [] in
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
              (let uu____10780 = prims.is lid in
               if uu____10780
               then
                 let vname = varops.new_fvar lid in
                 let uu____10785 = prims.mk lid vname in
                 match uu____10785 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10800 =
                    let uu____10806 = curried_arrow_formals_comp t_norm in
                    match uu____10806 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10817 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10817
                          then
                            let uu____10818 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10821 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10821.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10821.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10821.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10821.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10821.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10821.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10821.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10821.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10821.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10821.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10821.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10821.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10821.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10821.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10821.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10821.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10821.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10821.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10821.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10821.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10821.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10821.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10821.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10821.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10821.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10821.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10818
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10828 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10828)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10800 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10855 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10855 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10868 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10900  ->
                                     match uu___115_10900 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10903 =
                                           FStar_Util.prefix vars in
                                         (match uu____10903 with
                                          | (uu____10914,(xxsym,uu____10916))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10926 =
                                                let uu____10927 =
                                                  let uu____10931 =
                                                    let uu____10932 =
                                                      let uu____10938 =
                                                        let uu____10939 =
                                                          let uu____10942 =
                                                            let uu____10943 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10943 in
                                                          (vapp, uu____10942) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10939 in
                                                      ([[vapp]], vars,
                                                        uu____10938) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10932 in
                                                  (uu____10931,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10927 in
                                              [uu____10926])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10954 =
                                           FStar_Util.prefix vars in
                                         (match uu____10954 with
                                          | (uu____10965,(xxsym,uu____10967))
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
                                              let uu____10981 =
                                                let uu____10982 =
                                                  let uu____10986 =
                                                    let uu____10987 =
                                                      let uu____10993 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10993) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10987 in
                                                  (uu____10986,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10982 in
                                              [uu____10981])
                                     | uu____11002 -> [])) in
                           let uu____11003 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____11003 with
                            | (vars,guards,env',decls1,uu____11019) ->
                                let uu____11026 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____11031 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11031, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____11033 = encode_formula p env' in
                                      (match uu____11033 with
                                       | (g,ds) ->
                                           let uu____11040 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11040,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11026 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11049 =
                                         let uu____11053 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11053) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11049 in
                                     let uu____11058 =
                                       let vname_decl =
                                         let uu____11063 =
                                           let uu____11069 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11075  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11069,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11063 in
                                       let uu____11080 =
                                         let env2 =
                                           let uu___144_11084 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11084.bindings);
                                             depth = (uu___144_11084.depth);
                                             tcenv = (uu___144_11084.tcenv);
                                             warn = (uu___144_11084.warn);
                                             cache = (uu___144_11084.cache);
                                             nolabels =
                                               (uu___144_11084.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11084.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11084.current_module_name)
                                           } in
                                         let uu____11085 =
                                           let uu____11086 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11086 in
                                         if uu____11085
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____11080 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11096::uu____11097 ->
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
                                                   let uu____11120 =
                                                     let uu____11126 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11126) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11120 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11140 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11142 =
                                             match formals with
                                             | [] ->
                                                 let uu____11151 =
                                                   let uu____11152 =
                                                     let uu____11154 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____11154 in
                                                   push_free_var env1 lid
                                                     vname uu____11152 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11151)
                                             | uu____11157 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____11162 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11162 in
                                                 let name_tok_corr =
                                                   let uu____11164 =
                                                     let uu____11168 =
                                                       let uu____11169 =
                                                         let uu____11175 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11175) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11169 in
                                                     (uu____11168,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11164 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11142 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11058 with
                                      | (decls2,env2) ->
                                          let uu____11199 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11204 =
                                              encode_term res_t1 env' in
                                            match uu____11204 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11212 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11212,
                                                  decls) in
                                          (match uu____11199 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11220 =
                                                   let uu____11224 =
                                                     let uu____11225 =
                                                       let uu____11231 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11231) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11225 in
                                                   (uu____11224,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11220 in
                                               let freshness =
                                                 let uu____11240 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11240
                                                 then
                                                   let uu____11243 =
                                                     let uu____11244 =
                                                       let uu____11250 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____11256 =
                                                         varops.next_id () in
                                                       (vname, uu____11250,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11256) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11244 in
                                                   let uu____11258 =
                                                     let uu____11260 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11260] in
                                                   uu____11243 :: uu____11258
                                                 else [] in
                                               let g =
                                                 let uu____11264 =
                                                   let uu____11266 =
                                                     let uu____11268 =
                                                       let uu____11270 =
                                                         let uu____11272 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11272 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11270 in
                                                     FStar_List.append decls3
                                                       uu____11268 in
                                                   FStar_List.append decls2
                                                     uu____11266 in
                                                 FStar_List.append decls11
                                                   uu____11264 in
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
          let uu____11298 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11298 with
          | FStar_Pervasives_Native.None  ->
              let uu____11317 = encode_free_var env x t t_norm [] in
              (match uu____11317 with
               | (decls,env1) ->
                   let uu____11332 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11332 with
                    | (n1,x',uu____11347) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____11359) ->
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
          let uu____11396 = encode_free_var env lid t tt quals in
          match uu____11396 with
          | (decls,env1) ->
              let uu____11407 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11407
              then
                let uu____11411 =
                  let uu____11413 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11413 in
                (uu____11411, env1)
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
             (fun uu____11451  ->
                fun lb  ->
                  match uu____11451 with
                  | (decls,env1) ->
                      let uu____11463 =
                        let uu____11467 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11467
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11463 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11482 = FStar_Syntax_Util.head_and_args t in
    match uu____11482 with
    | (hd1,args) ->
        let uu____11508 =
          let uu____11509 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11509.FStar_Syntax_Syntax.n in
        (match uu____11508 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11513,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11526 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____11544  ->
      fun quals  ->
        match uu____11544 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11594 = FStar_Util.first_N nbinders formals in
              match uu____11594 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11643  ->
                         fun uu____11644  ->
                           match (uu____11643, uu____11644) with
                           | ((formal,uu____11654),(binder,uu____11656)) ->
                               let uu____11661 =
                                 let uu____11666 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11666) in
                               FStar_Syntax_Syntax.NT uu____11661) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11671 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11689  ->
                              match uu____11689 with
                              | (x,i) ->
                                  let uu____11696 =
                                    let uu___145_11697 = x in
                                    let uu____11698 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11697.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11697.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11698
                                    } in
                                  (uu____11696, i))) in
                    FStar_All.pipe_right uu____11671
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11710 =
                      let uu____11712 =
                        let uu____11713 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11713.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____11712 in
                    let uu____11717 =
                      let uu____11718 = FStar_Syntax_Subst.compress body in
                      let uu____11719 =
                        let uu____11720 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____11720 in
                      FStar_Syntax_Syntax.extend_app_n uu____11718
                        uu____11719 in
                    uu____11717 uu____11710 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11762 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11762
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11765 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11765.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11765.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11765.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11765.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11765.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11765.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11765.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11765.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11765.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11765.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11765.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11765.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11765.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11765.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11765.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11765.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11765.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11765.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11765.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11765.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11765.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11765.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11765.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11765.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11765.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11765.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11786 = FStar_Syntax_Util.abs_formals e in
                match uu____11786 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11820::uu____11821 ->
                         let uu____11829 =
                           let uu____11830 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11830.FStar_Syntax_Syntax.n in
                         (match uu____11829 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11857 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11857 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11885 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11885
                                   then
                                     let uu____11908 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11908 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11963  ->
                                                   fun uu____11964  ->
                                                     match (uu____11963,
                                                             uu____11964)
                                                     with
                                                     | ((x,uu____11974),
                                                        (b,uu____11976)) ->
                                                         let uu____11981 =
                                                           let uu____11986 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11986) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11981)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11988 =
                                            let uu____11999 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11999) in
                                          (uu____11988, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12039 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12039 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12091) ->
                              let uu____12096 =
                                let uu____12107 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____12107 in
                              (uu____12096, true)
                          | uu____12140 when Prims.op_Negation norm1 ->
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
                          | uu____12142 ->
                              let uu____12143 =
                                let uu____12144 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12145 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12144
                                  uu____12145 in
                              failwith uu____12143)
                     | uu____12158 ->
                         let uu____12159 =
                           let uu____12160 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12160.FStar_Syntax_Syntax.n in
                         (match uu____12159 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12187 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12187 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12205 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12205 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12253 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12283 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12283
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12291 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12345  ->
                            fun lb  ->
                              match uu____12345 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12396 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12396
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____12399 =
                                      let uu____12407 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12407
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12399 with
                                    | (tok,decl,env2) ->
                                        let uu____12432 =
                                          let uu____12439 =
                                            let uu____12445 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12445, tok) in
                                          uu____12439 :: toks in
                                        (uu____12432, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12291 with
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
                        | uu____12547 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____12552 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12552 vars)
                            else
                              (let uu____12554 =
                                 let uu____12558 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12558) in
                               FStar_SMTEncoding_Util.mkApp uu____12554) in
                      let uu____12563 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_12566  ->
                                 match uu___116_12566 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12567 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12572 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12572))) in
                      if uu____12563
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12592;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12594;
                                FStar_Syntax_Syntax.lbeff = uu____12595;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12632 =
                                 let uu____12636 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12636 with
                                 | (tcenv',uu____12647,e_t) ->
                                     let uu____12651 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12658 -> failwith "Impossible" in
                                     (match uu____12651 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12668 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12668.bindings);
                                              depth = (uu___149_12668.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12668.warn);
                                              cache = (uu___149_12668.cache);
                                              nolabels =
                                                (uu___149_12668.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12668.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12668.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12668.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12632 with
                                | (env',e1,t_norm1) ->
                                    let uu____12675 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12675 with
                                     | ((binders,body,uu____12687,uu____12688),curry)
                                         ->
                                         ((let uu____12695 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12695
                                           then
                                             let uu____12696 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12697 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12696 uu____12697
                                           else ());
                                          (let uu____12699 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____12699 with
                                           | (vars,guards,env'1,binder_decls,uu____12715)
                                               ->
                                               let body1 =
                                                 let uu____12723 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12723
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12726 =
                                                 let uu____12731 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12731
                                                 then
                                                   let uu____12737 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12738 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12737, uu____12738)
                                                 else
                                                   (let uu____12744 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12744)) in
                                               (match uu____12726 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12758 =
                                                        let uu____12762 =
                                                          let uu____12763 =
                                                            let uu____12769 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12769) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12763 in
                                                        let uu____12775 =
                                                          let uu____12777 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____12777 in
                                                        (uu____12762,
                                                          uu____12775,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12758 in
                                                    let uu____12779 =
                                                      let uu____12781 =
                                                        let uu____12783 =
                                                          let uu____12785 =
                                                            let uu____12787 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12787 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12785 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12783 in
                                                      FStar_List.append
                                                        decls1 uu____12781 in
                                                    (uu____12779, env1))))))
                           | uu____12790 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12809 = varops.fresh "fuel" in
                             (uu____12809, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12812 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12862  ->
                                     fun uu____12863  ->
                                       match (uu____12862, uu____12863) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12941 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12941 in
                                           let gtok =
                                             let uu____12943 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12943 in
                                           let env3 =
                                             let uu____12945 =
                                               let uu____12947 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____12947 in
                                             push_free_var env2 flid gtok
                                               uu____12945 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12812 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13033
                                 t_norm uu____13035 =
                                 match (uu____13033, uu____13035) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13062;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13063;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13080 =
                                       let uu____13084 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13084 with
                                       | (tcenv',uu____13099,e_t) ->
                                           let uu____13103 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13110 ->
                                                 failwith "Impossible" in
                                           (match uu____13103 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13120 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13120.bindings);
                                                    depth =
                                                      (uu___150_13120.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13120.warn);
                                                    cache =
                                                      (uu___150_13120.cache);
                                                    nolabels =
                                                      (uu___150_13120.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13120.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13120.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13120.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13080 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13130 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13130
                                            then
                                              let uu____13131 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13132 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13133 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13131 uu____13132
                                                uu____13133
                                            else ());
                                           (let uu____13135 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13135 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13157 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13157
                                                  then
                                                    let uu____13158 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13159 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13160 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13161 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13158 uu____13159
                                                      uu____13160 uu____13161
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13165 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____13165 with
                                                  | (vars,guards,env'1,binder_decls,uu____13183)
                                                      ->
                                                      let decl_g =
                                                        let uu____13191 =
                                                          let uu____13197 =
                                                            let uu____13199 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13199 in
                                                          (g, uu____13197,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13191 in
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
                                                        let uu____13214 =
                                                          let uu____13218 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13218) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13214 in
                                                      let gsapp =
                                                        let uu____13224 =
                                                          let uu____13228 =
                                                            let uu____13230 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13230 ::
                                                              vars_tm in
                                                          (g, uu____13228) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13224 in
                                                      let gmax =
                                                        let uu____13234 =
                                                          let uu____13238 =
                                                            let uu____13240 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13240 ::
                                                              vars_tm in
                                                          (g, uu____13238) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13234 in
                                                      let body1 =
                                                        let uu____13244 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13244
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13246 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13246 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13257
                                                               =
                                                               let uu____13261
                                                                 =
                                                                 let uu____13262
                                                                   =
                                                                   let uu____13270
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
                                                                    uu____13270) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13262 in
                                                               let uu____13281
                                                                 =
                                                                 let uu____13283
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____13283 in
                                                               (uu____13261,
                                                                 uu____13281,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13257 in
                                                           let eqn_f =
                                                             let uu____13286
                                                               =
                                                               let uu____13290
                                                                 =
                                                                 let uu____13291
                                                                   =
                                                                   let uu____13297
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13297) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13291 in
                                                               (uu____13290,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13286 in
                                                           let eqn_g' =
                                                             let uu____13305
                                                               =
                                                               let uu____13309
                                                                 =
                                                                 let uu____13310
                                                                   =
                                                                   let uu____13316
                                                                    =
                                                                    let uu____13317
                                                                    =
                                                                    let uu____13320
                                                                    =
                                                                    let uu____13321
                                                                    =
                                                                    let uu____13325
                                                                    =
                                                                    let uu____13327
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13327
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13325) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13321 in
                                                                    (gsapp,
                                                                    uu____13320) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13317 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13316) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13310 in
                                                               (uu____13309,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13305 in
                                                           let uu____13339 =
                                                             let uu____13344
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____13344
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13361)
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
                                                                    let uu____13376
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____13376
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13379
                                                                    =
                                                                    let uu____13383
                                                                    =
                                                                    let uu____13384
                                                                    =
                                                                    let uu____13390
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13390) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13384 in
                                                                    (uu____13383,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13379 in
                                                                 let uu____13401
                                                                   =
                                                                   let uu____13405
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____13405
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13413
                                                                    =
                                                                    let uu____13415
                                                                    =
                                                                    let uu____13416
                                                                    =
                                                                    let uu____13420
                                                                    =
                                                                    let uu____13421
                                                                    =
                                                                    let uu____13427
                                                                    =
                                                                    let uu____13428
                                                                    =
                                                                    let uu____13431
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13431,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13428 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13427) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13421 in
                                                                    (uu____13420,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13416 in
                                                                    [uu____13415] in
                                                                    (d3,
                                                                    uu____13413) in
                                                                 (match uu____13401
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____13339
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
                               let uu____13466 =
                                 let uu____13473 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13521  ->
                                      fun uu____13522  ->
                                        match (uu____13521, uu____13522) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13608 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13608 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13473 in
                               (match uu____13466 with
                                | (decls2,eqns,env01) ->
                                    let uu____13648 =
                                      let isDeclFun uu___117_13656 =
                                        match uu___117_13656 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13657 -> true
                                        | uu____13663 -> false in
                                      let uu____13664 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13664
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13648 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13694 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13694
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
        let uu____13728 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13728 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____13731 = encode_sigelt' env se in
      match uu____13731 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13741 =
                  let uu____13742 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13742 in
                [uu____13741]
            | uu____13743 ->
                let uu____13744 =
                  let uu____13746 =
                    let uu____13747 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13747 in
                  uu____13746 :: g in
                let uu____13748 =
                  let uu____13750 =
                    let uu____13751 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13751 in
                  [uu____13750] in
                FStar_List.append uu____13744 uu____13748 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13761 =
          let uu____13762 = FStar_Syntax_Subst.compress t in
          uu____13762.FStar_Syntax_Syntax.n in
        match uu____13761 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13766)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13769 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13772 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13775 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13777 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13779 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13787 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13790 =
            let uu____13791 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13791 Prims.op_Negation in
          if uu____13790
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13811 ->
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
               let uu____13831 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13831 with
               | (aname,atok,env2) ->
                   let uu____13841 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13841 with
                    | (formals,uu____13851) ->
                        let uu____13858 =
                          let uu____13861 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13861 env2 in
                        (match uu____13858 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13869 =
                                 let uu____13870 =
                                   let uu____13876 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13885  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13876,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13870 in
                               [uu____13869;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____13892 =
                               let aux uu____13921 uu____13922 =
                                 match (uu____13921, uu____13922) with
                                 | ((bv,uu____13949),(env3,acc_sorts,acc)) ->
                                     let uu____13970 = gen_term_var env3 bv in
                                     (match uu____13970 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13892 with
                              | (uu____14008,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14022 =
                                      let uu____14026 =
                                        let uu____14027 =
                                          let uu____14033 =
                                            let uu____14034 =
                                              let uu____14037 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14037) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14034 in
                                          ([[app]], xs_sorts, uu____14033) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14027 in
                                      (uu____14026,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14022 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14049 =
                                      let uu____14053 =
                                        let uu____14054 =
                                          let uu____14060 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14060) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14054 in
                                      (uu____14053,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14049 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14070 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14070 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14086,uu____14087)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____14088 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14088 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14099,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14104 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_14107  ->
                      match uu___118_14107 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14108 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14111 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14112 -> false)) in
            Prims.op_Negation uu____14104 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____14118 = encode_top_level_val env fv t quals in
             match uu____14118 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14130 =
                   let uu____14132 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14132 in
                 (uu____14130, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____14138 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____14138 with
           | (uu____14143,f1) ->
               let uu____14145 = encode_formula f1 env in
               (match uu____14145 with
                | (f2,decls) ->
                    let g =
                      let uu____14154 =
                        let uu____14155 =
                          let uu____14159 =
                            let uu____14161 =
                              let uu____14162 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____14162 in
                            FStar_Pervasives_Native.Some uu____14161 in
                          let uu____14163 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____14159, uu____14163) in
                        FStar_SMTEncoding_Util.mkAssume uu____14155 in
                      [uu____14154] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14167) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____14174 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14189 =
                       let uu____14191 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14191.FStar_Syntax_Syntax.fv_name in
                     uu____14189.FStar_Syntax_Syntax.v in
                   let uu____14192 =
                     let uu____14193 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14193 in
                   if uu____14192
                   then
                     let val_decl =
                       let uu___151_14208 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14208.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14208.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14208.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____14212 = encode_sigelt' env1 val_decl in
                     match uu____14212 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____14174 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14229,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14231;
                          FStar_Syntax_Syntax.lbtyp = uu____14232;
                          FStar_Syntax_Syntax.lbeff = uu____14233;
                          FStar_Syntax_Syntax.lbdef = uu____14234;_}::[]),uu____14235)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____14247 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14247 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14266 =
                   let uu____14268 =
                     let uu____14269 =
                       let uu____14273 =
                         let uu____14274 =
                           let uu____14280 =
                             let uu____14281 =
                               let uu____14284 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14284) in
                             FStar_SMTEncoding_Util.mkEq uu____14281 in
                           ([[b2t_x]], [xx], uu____14280) in
                         FStar_SMTEncoding_Util.mkForall uu____14274 in
                       (uu____14273,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14269 in
                   [uu____14268] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____14266 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14301,uu____14302) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14308  ->
                  match uu___119_14308 with
                  | FStar_Syntax_Syntax.Discriminator uu____14309 -> true
                  | uu____14310 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14312,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14320 =
                     let uu____14321 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14321.FStar_Ident.idText in
                   uu____14320 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14324  ->
                     match uu___120_14324 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14325 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14328) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_14338  ->
                  match uu___121_14338 with
                  | FStar_Syntax_Syntax.Projector uu____14339 -> true
                  | uu____14342 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14345 = try_lookup_free_var env l in
          (match uu____14345 with
           | FStar_Pervasives_Native.Some uu____14349 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_14352 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14352.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14352.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_14352.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____14358) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14368) ->
          let uu____14373 = encode_sigelts env ses in
          (match uu____14373 with
           | (g,env1) ->
               let uu____14383 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_14397  ->
                         match uu___122_14397 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14398;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14399;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14400;_}
                             -> false
                         | uu____14402 -> true)) in
               (match uu____14383 with
                | (g',inversions) ->
                    let uu____14411 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_14423  ->
                              match uu___123_14423 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14424 ->
                                  true
                              | uu____14430 -> false)) in
                    (match uu____14411 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14441,tps,k,uu____14444,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_14455  ->
                    match uu___124_14455 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14456 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14463 = c in
              match uu____14463 with
              | (name,args,uu____14467,uu____14468,uu____14469) ->
                  let uu____14472 =
                    let uu____14473 =
                      let uu____14479 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14490  ->
                                match uu____14490 with
                                | (uu____14494,sort,uu____14496) -> sort)) in
                      (name, uu____14479, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14473 in
                  [uu____14472]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14514 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14519 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14519 FStar_Option.isNone)) in
            if uu____14514
            then []
            else
              (let uu____14536 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14536 with
               | (xxsym,xx) ->
                   let uu____14542 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14571  ->
                             fun l  ->
                               match uu____14571 with
                               | (out,decls) ->
                                   let uu____14583 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14583 with
                                    | (uu____14589,data_t) ->
                                        let uu____14591 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14591 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14620 =
                                                 let uu____14621 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14621.FStar_Syntax_Syntax.n in
                                               match uu____14620 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14629,indices) ->
                                                   indices
                                               | uu____14645 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14662  ->
                                                         match uu____14662
                                                         with
                                                         | (x,uu____14666) ->
                                                             let uu____14667
                                                               =
                                                               let uu____14668
                                                                 =
                                                                 let uu____14672
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14672,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14668 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14667)
                                                    env) in
                                             let uu____14674 =
                                               encode_args indices env1 in
                                             (match uu____14674 with
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
                                                      let uu____14698 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14709
                                                                 =
                                                                 let uu____14712
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14712,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14709)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14698
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14714 =
                                                      let uu____14715 =
                                                        let uu____14718 =
                                                          let uu____14719 =
                                                            let uu____14722 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14722,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14719 in
                                                        (out, uu____14718) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14715 in
                                                    (uu____14714,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14542 with
                    | (data_ax,decls) ->
                        let uu____14730 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14730 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14744 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14744 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14747 =
                                 let uu____14751 =
                                   let uu____14752 =
                                     let uu____14758 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14766 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14758,
                                       uu____14766) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14752 in
                                 let uu____14774 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14751,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____14774) in
                               FStar_SMTEncoding_Util.mkAssume uu____14747 in
                             let pattern_guarded_inversion =
                               let uu____14778 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14778
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14789 =
                                   let uu____14790 =
                                     let uu____14794 =
                                       let uu____14795 =
                                         let uu____14801 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14809 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14801, uu____14809) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14795 in
                                     let uu____14817 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14794,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____14817) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14790 in
                                 [uu____14789]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14820 =
            let uu____14828 =
              let uu____14829 = FStar_Syntax_Subst.compress k in
              uu____14829.FStar_Syntax_Syntax.n in
            match uu____14828 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14858 -> (tps, k) in
          (match uu____14820 with
           | (formals,res) ->
               let uu____14873 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14873 with
                | (formals1,res1) ->
                    let uu____14880 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____14880 with
                     | (vars,guards,env',binder_decls,uu____14895) ->
                         let uu____14902 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14902 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14915 =
                                  let uu____14919 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14919) in
                                FStar_SMTEncoding_Util.mkApp uu____14915 in
                              let uu____14924 =
                                let tname_decl =
                                  let uu____14930 =
                                    let uu____14931 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14949  ->
                                              match uu____14949 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14957 = varops.next_id () in
                                    (tname, uu____14931,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14957, false) in
                                  constructor_or_logic_type_decl uu____14930 in
                                let uu____14962 =
                                  match vars with
                                  | [] ->
                                      let uu____14969 =
                                        let uu____14970 =
                                          let uu____14972 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____14972 in
                                        push_free_var env1 t tname
                                          uu____14970 in
                                      ([], uu____14969)
                                  | uu____14976 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____14982 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14982 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14991 =
                                          let uu____14995 =
                                            let uu____14996 =
                                              let uu____15004 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____15004) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14996 in
                                          (uu____14995,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14991 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14962 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14924 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15027 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____15027 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15044 =
                                               let uu____15045 =
                                                 let uu____15049 =
                                                   let uu____15050 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15050 in
                                                 (uu____15049,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15045 in
                                             [uu____15044]
                                           else [] in
                                         let uu____15053 =
                                           let uu____15055 =
                                             let uu____15057 =
                                               let uu____15058 =
                                                 let uu____15062 =
                                                   let uu____15063 =
                                                     let uu____15069 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15069) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15063 in
                                                 (uu____15062,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15058 in
                                             [uu____15057] in
                                           FStar_List.append karr uu____15055 in
                                         FStar_List.append decls1 uu____15053 in
                                   let aux =
                                     let uu____15078 =
                                       let uu____15080 =
                                         inversion_axioms tapp vars in
                                       let uu____15082 =
                                         let uu____15084 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15084] in
                                       FStar_List.append uu____15080
                                         uu____15082 in
                                     FStar_List.append kindingAx uu____15078 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15089,uu____15090,uu____15091,uu____15092,uu____15093)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15098,t,uu____15100,n_tps,uu____15102) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15107 = new_term_constant_and_tok_from_lid env d in
          (match uu____15107 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15118 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15118 with
                | (formals,t_res) ->
                    let uu____15140 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15140 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15149 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____15149 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15191 =
                                            mk_term_projector_name d x in
                                          (uu____15191,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15193 =
                                  let uu____15203 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15203, true) in
                                FStar_All.pipe_right uu____15193
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
                              let uu____15225 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____15225 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15233::uu____15234 ->
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
                                         let uu____15259 =
                                           let uu____15265 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15265) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15259
                                     | uu____15278 -> tok_typing in
                                   let uu____15283 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____15283 with
                                    | (vars',guards',env'',decls_formals,uu____15298)
                                        ->
                                        let uu____15305 =
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
                                        (match uu____15305 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15324 ->
                                                   let uu____15328 =
                                                     let uu____15329 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15329 in
                                                   [uu____15328] in
                                             let encode_elim uu____15336 =
                                               let uu____15337 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15337 with
                                               | (head1,args) ->
                                                   let uu____15366 =
                                                     let uu____15367 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15367.FStar_Syntax_Syntax.n in
                                                   (match uu____15366 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15374;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15375;_},uu____15376)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15381 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15381
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
                                                                 | uu____15410
                                                                    ->
                                                                    let uu____15411
                                                                    =
                                                                    let uu____15412
                                                                    =
                                                                    let uu____15415
                                                                    =
                                                                    let uu____15416
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15416 in
                                                                    (uu____15415,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15412 in
                                                                    raise
                                                                    uu____15411 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15427
                                                                    =
                                                                    let uu____15428
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15428 in
                                                                    if
                                                                    uu____15427
                                                                    then
                                                                    let uu____15435
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15435]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15437
                                                               =
                                                               let uu____15444
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15477
                                                                     ->
                                                                    fun
                                                                    uu____15478
                                                                     ->
                                                                    match 
                                                                    (uu____15477,
                                                                    uu____15478)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15529
                                                                    =
                                                                    let uu____15533
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15533 in
                                                                    (match uu____15529
                                                                    with
                                                                    | 
                                                                    (uu____15540,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15546
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15546
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15548
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15548
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
                                                                 uu____15444 in
                                                             (match uu____15437
                                                              with
                                                              | (uu____15556,arg_vars,elim_eqns_or_guards,uu____15559)
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
                                                                    let uu____15578
                                                                    =
                                                                    let uu____15582
                                                                    =
                                                                    let uu____15583
                                                                    =
                                                                    let uu____15589
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15595
                                                                    =
                                                                    let uu____15596
                                                                    =
                                                                    let uu____15599
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15599) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15596 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15589,
                                                                    uu____15595) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15583 in
                                                                    (uu____15582,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15578 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15612
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15612,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15614
                                                                    =
                                                                    let uu____15618
                                                                    =
                                                                    let uu____15619
                                                                    =
                                                                    let uu____15625
                                                                    =
                                                                    let uu____15628
                                                                    =
                                                                    let uu____15630
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15630] in
                                                                    [uu____15628] in
                                                                    let uu____15633
                                                                    =
                                                                    let uu____15634
                                                                    =
                                                                    let uu____15637
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15638
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15637,
                                                                    uu____15638) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15634 in
                                                                    (uu____15625,
                                                                    [x],
                                                                    uu____15633) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15619 in
                                                                    let uu____15648
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15618,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15648) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15614
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15653
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
                                                                    (let uu____15670
                                                                    =
                                                                    let uu____15671
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15671
                                                                    dapp1 in
                                                                    [uu____15670]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15653
                                                                    FStar_List.flatten in
                                                                    let uu____15675
                                                                    =
                                                                    let uu____15679
                                                                    =
                                                                    let uu____15680
                                                                    =
                                                                    let uu____15686
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15692
                                                                    =
                                                                    let uu____15693
                                                                    =
                                                                    let uu____15696
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15696) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15693 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15686,
                                                                    uu____15692) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15680 in
                                                                    (uu____15679,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15675) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15708 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15708
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
                                                                 | uu____15737
                                                                    ->
                                                                    let uu____15738
                                                                    =
                                                                    let uu____15739
                                                                    =
                                                                    let uu____15742
                                                                    =
                                                                    let uu____15743
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15743 in
                                                                    (uu____15742,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15739 in
                                                                    raise
                                                                    uu____15738 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15754
                                                                    =
                                                                    let uu____15755
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15755 in
                                                                    if
                                                                    uu____15754
                                                                    then
                                                                    let uu____15762
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15762]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15764
                                                               =
                                                               let uu____15771
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15804
                                                                     ->
                                                                    fun
                                                                    uu____15805
                                                                     ->
                                                                    match 
                                                                    (uu____15804,
                                                                    uu____15805)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15856
                                                                    =
                                                                    let uu____15860
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15860 in
                                                                    (match uu____15856
                                                                    with
                                                                    | 
                                                                    (uu____15867,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15873
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15873
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15875
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15875
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
                                                                 uu____15771 in
                                                             (match uu____15764
                                                              with
                                                              | (uu____15883,arg_vars,elim_eqns_or_guards,uu____15886)
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
                                                                    let uu____15905
                                                                    =
                                                                    let uu____15909
                                                                    =
                                                                    let uu____15910
                                                                    =
                                                                    let uu____15916
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15922
                                                                    =
                                                                    let uu____15923
                                                                    =
                                                                    let uu____15926
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15926) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15923 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15916,
                                                                    uu____15922) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15910 in
                                                                    (uu____15909,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15905 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15939
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15939,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15941
                                                                    =
                                                                    let uu____15945
                                                                    =
                                                                    let uu____15946
                                                                    =
                                                                    let uu____15952
                                                                    =
                                                                    let uu____15955
                                                                    =
                                                                    let uu____15957
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15957] in
                                                                    [uu____15955] in
                                                                    let uu____15960
                                                                    =
                                                                    let uu____15961
                                                                    =
                                                                    let uu____15964
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15965
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15964,
                                                                    uu____15965) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15961 in
                                                                    (uu____15952,
                                                                    [x],
                                                                    uu____15960) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15946 in
                                                                    let uu____15975
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15945,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15975) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15941
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15980
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
                                                                    (let uu____15997
                                                                    =
                                                                    let uu____15998
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15998
                                                                    dapp1 in
                                                                    [uu____15997]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15980
                                                                    FStar_List.flatten in
                                                                    let uu____16002
                                                                    =
                                                                    let uu____16006
                                                                    =
                                                                    let uu____16007
                                                                    =
                                                                    let uu____16013
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16019
                                                                    =
                                                                    let uu____16020
                                                                    =
                                                                    let uu____16023
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16023) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16020 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16013,
                                                                    uu____16019) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16007 in
                                                                    (uu____16006,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16002) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16033 ->
                                                        ((let uu____16035 =
                                                            let uu____16036 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16037 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16036
                                                              uu____16037 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16035);
                                                         ([], []))) in
                                             let uu____16040 = encode_elim () in
                                             (match uu____16040 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16052 =
                                                      let uu____16054 =
                                                        let uu____16056 =
                                                          let uu____16058 =
                                                            let uu____16060 =
                                                              let uu____16061
                                                                =
                                                                let uu____16067
                                                                  =
                                                                  let uu____16069
                                                                    =
                                                                    let uu____16070
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16070 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16069 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16067) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16061 in
                                                            [uu____16060] in
                                                          let uu____16073 =
                                                            let uu____16075 =
                                                              let uu____16077
                                                                =
                                                                let uu____16079
                                                                  =
                                                                  let uu____16081
                                                                    =
                                                                    let uu____16083
                                                                    =
                                                                    let uu____16085
                                                                    =
                                                                    let uu____16086
                                                                    =
                                                                    let uu____16090
                                                                    =
                                                                    let uu____16091
                                                                    =
                                                                    let uu____16097
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16097) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16091 in
                                                                    (uu____16090,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16086 in
                                                                    let uu____16104
                                                                    =
                                                                    let uu____16106
                                                                    =
                                                                    let uu____16107
                                                                    =
                                                                    let uu____16111
                                                                    =
                                                                    let uu____16112
                                                                    =
                                                                    let uu____16118
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16124
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16118,
                                                                    uu____16124) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16112 in
                                                                    (uu____16111,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16107 in
                                                                    [uu____16106] in
                                                                    uu____16085
                                                                    ::
                                                                    uu____16104 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16083 in
                                                                  FStar_List.append
                                                                    uu____16081
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16079 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16077 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16075 in
                                                          FStar_List.append
                                                            uu____16058
                                                            uu____16073 in
                                                        FStar_List.append
                                                          decls3 uu____16056 in
                                                      FStar_List.append
                                                        decls2 uu____16054 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16052 in
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
           (fun uu____16152  ->
              fun se  ->
                match uu____16152 with
                | (g,env1) ->
                    let uu____16164 = encode_sigelt env1 se in
                    (match uu____16164 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16202 =
        match uu____16202 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16220 ->
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
                 ((let uu____16225 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16225
                   then
                     let uu____16226 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16227 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16228 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16226 uu____16227 uu____16228
                   else ());
                  (let uu____16230 = encode_term t1 env1 in
                   match uu____16230 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16240 =
                         let uu____16244 =
                           let uu____16245 =
                             let uu____16246 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16246
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16245 in
                         new_term_constant_from_string env1 x uu____16244 in
                       (match uu____16240 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____16257 = FStar_Options.log_queries () in
                              if uu____16257
                              then
                                let uu____16259 =
                                  let uu____16260 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16261 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16262 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16260 uu____16261 uu____16262 in
                                FStar_Pervasives_Native.Some uu____16259
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16273,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____16282 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16282 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16295,se,uu____16297) ->
                 let uu____16300 = encode_sigelt env1 se in
                 (match uu____16300 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16310,se) ->
                 let uu____16314 = encode_sigelt env1 se in
                 (match uu____16314 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16324 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16324 with | (uu____16336,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16388  ->
            match uu____16388 with
            | (l,uu____16395,uu____16396) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16423  ->
            match uu____16423 with
            | (l,uu____16431,uu____16432) ->
                let uu____16437 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____16438 =
                  let uu____16440 =
                    let uu____16441 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16441 in
                  [uu____16440] in
                uu____16437 :: uu____16438)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16453 =
      let uu____16455 =
        let uu____16456 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16458 =
          let uu____16459 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16459 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16456;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16458
        } in
      [uu____16455] in
    FStar_ST.write last_env uu____16453
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16471 = FStar_ST.read last_env in
      match uu____16471 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16477 ->
          let uu___153_16479 = e in
          let uu____16480 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_16479.bindings);
            depth = (uu___153_16479.depth);
            tcenv;
            warn = (uu___153_16479.warn);
            cache = (uu___153_16479.cache);
            nolabels = (uu___153_16479.nolabels);
            use_zfuel_name = (uu___153_16479.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16479.encode_non_total_function_typ);
            current_module_name = uu____16480
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____16485 = FStar_ST.read last_env in
    match uu____16485 with
    | [] -> failwith "Empty env stack"
    | uu____16490::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16499  ->
    let uu____16500 = FStar_ST.read last_env in
    match uu____16500 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_16511 = hd1 in
          {
            bindings = (uu___154_16511.bindings);
            depth = (uu___154_16511.depth);
            tcenv = (uu___154_16511.tcenv);
            warn = (uu___154_16511.warn);
            cache = refs;
            nolabels = (uu___154_16511.nolabels);
            use_zfuel_name = (uu___154_16511.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16511.encode_non_total_function_typ);
            current_module_name = (uu___154_16511.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16518  ->
    let uu____16519 = FStar_ST.read last_env in
    match uu____16519 with
    | [] -> failwith "Popping an empty stack"
    | uu____16524::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16533  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16537  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16541  ->
    let uu____16542 = FStar_ST.read last_env in
    match uu____16542 with
    | hd1::uu____16548::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16554 -> failwith "Impossible"
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
        | (uu____16613::uu____16614,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16620 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16620.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16620.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16620.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16621 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16634 =
        let uu____16636 =
          let uu____16637 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16637 in
        let uu____16638 = open_fact_db_tags env in uu____16636 :: uu____16638 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16634
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
      let uu____16655 = encode_sigelt env se in
      match uu____16655 with
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
        let uu____16682 = FStar_Options.log_queries () in
        if uu____16682
        then
          let uu____16684 =
            let uu____16685 =
              let uu____16686 =
                let uu____16687 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16687 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16686 in
            FStar_SMTEncoding_Term.Caption uu____16685 in
          uu____16684 :: decls
        else decls in
      let env =
        let uu____16694 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16694 tcenv in
      let uu____16695 = encode_top_level_facts env se in
      match uu____16695 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16704 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16704))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16717 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16717
       then
         let uu____16718 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16718
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16748  ->
                 fun se  ->
                   match uu____16748 with
                   | (g,env2) ->
                       let uu____16760 = encode_top_level_facts env2 se in
                       (match uu____16760 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16773 =
         encode_signature
           (let uu___156_16779 = env in
            {
              bindings = (uu___156_16779.bindings);
              depth = (uu___156_16779.depth);
              tcenv = (uu___156_16779.tcenv);
              warn = false;
              cache = (uu___156_16779.cache);
              nolabels = (uu___156_16779.nolabels);
              use_zfuel_name = (uu___156_16779.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16779.encode_non_total_function_typ);
              current_module_name = (uu___156_16779.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16773 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16791 = FStar_Options.log_queries () in
             if uu____16791
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16798 = env1 in
               {
                 bindings = (uu___157_16798.bindings);
                 depth = (uu___157_16798.depth);
                 tcenv = (uu___157_16798.tcenv);
                 warn = true;
                 cache = (uu___157_16798.cache);
                 nolabels = (uu___157_16798.nolabels);
                 use_zfuel_name = (uu___157_16798.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16798.encode_non_total_function_typ);
                 current_module_name = (uu___157_16798.current_module_name)
               });
            (let uu____16800 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16800
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
        (let uu____16838 =
           let uu____16839 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16839.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16838);
        (let env =
           let uu____16841 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16841 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16850 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16871 = aux rest in
                 (match uu____16871 with
                  | (out,rest1) ->
                      let t =
                        let uu____16889 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16889 with
                        | FStar_Pervasives_Native.Some uu____16893 ->
                            let uu____16894 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16894
                              x.FStar_Syntax_Syntax.sort
                        | uu____16895 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16898 =
                        let uu____16900 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16903 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16903.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16903.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16900 :: out in
                      (uu____16898, rest1))
             | uu____16906 -> ([], bindings1) in
           let uu____16910 = aux bindings in
           match uu____16910 with
           | (closing,bindings1) ->
               let uu____16924 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16924, bindings1) in
         match uu____16850 with
         | (q1,bindings1) ->
             let uu____16937 =
               let uu____16940 =
                 FStar_List.filter
                   (fun uu___125_16944  ->
                      match uu___125_16944 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16945 ->
                          false
                      | uu____16949 -> true) bindings1 in
               encode_env_bindings env uu____16940 in
             (match uu____16937 with
              | (env_decls,env1) ->
                  ((let uu____16960 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16960
                    then
                      let uu____16961 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16961
                    else ());
                   (let uu____16963 = encode_formula q1 env1 in
                    match uu____16963 with
                    | (phi,qdecls) ->
                        let uu____16975 =
                          let uu____16978 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16978 phi in
                        (match uu____16975 with
                         | (labels,phi1) ->
                             let uu____16988 = encode_labels labels in
                             (match uu____16988 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____17009 =
                                      let uu____17013 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____17014 =
                                        varops.mk_unique "@query" in
                                      (uu____17013,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17014) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17009 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____17029 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17029 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____17031 = encode_formula q env in
       match uu____17031 with
       | (f,uu____17035) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____17037) -> true
             | uu____17040 -> false)))